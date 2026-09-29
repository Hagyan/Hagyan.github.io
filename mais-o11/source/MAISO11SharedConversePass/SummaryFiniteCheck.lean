import Std

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 10000000

namespace MAISO11.SummaryFiniteCheck

structure Summary where
  len : Nat
  closes : Nat
  opens : Nat
  deriving DecidableEq, Repr

inductive Atom where
  | ref : Nat → Atom
  | lit : Char → Atom
  deriving DecidableEq, Repr

structure Gate where
  left : Summary
  right : Summary
  result : Summary
  deriving DecidableEq, Repr

def emptySummary : Summary := ⟨0, 0, 0⟩

def charSummary : Char → Summary
  | '(' => ⟨1, 0, 1⟩
  | ')' => ⟨1, 1, 0⟩
  | _ => ⟨1, 0, 0⟩

def itemSummary (done : List Summary) : Atom → Summary
  | .ref i => done.getD i emptySummary
  | .lit c => charSummary c

def joinSummary (x y : Summary) : Summary :=
  let c := min x.opens y.closes
  let u := x.opens - c
  let v := y.closes - c
  ⟨x.len + y.len, x.closes + v, u + y.opens⟩

def foldRhs (done : List Summary) (acc : Summary) : List Atom → Summary
  | [] => acc
  | a :: rest => foldRhs done (joinSummary acc (itemSummary done a)) rest

def summarizeRules : List (List Atom) → List Summary → List Summary
  | [], done => done
  | rhs :: rest, done =>
      let result := foldRhs done emptySummary rhs
      summarizeRules rest (done ++ [result])

def scanRhs (done : List Summary) (acc : Summary) : List Atom → List Gate
  | [] => []
  | a :: rest =>
      let right := itemSummary done a
      let result := joinSummary acc right
      ⟨acc, right, result⟩ :: scanRhs done result rest

def buildGates : List (List Atom) → List Summary → List Gate
  | [], _ => []
  | rhs :: rest, done =>
      let result := foldRhs done emptySummary rhs
      scanRhs done emptySummary rhs ++ buildGates rest (done ++ [result])

def atomWellFormed (current : Nat) : Atom → Bool
  | .ref i => decide (i < current)
  | .lit c => decide (c = '(' ∨ c = ')' ∨ c = 'x')

def grammarWellFormed : Nat → List (List Atom) → Bool
  | _, [] => true
  | i, rhs :: rest => rhs.all (atomWellFormed i) && grammarWellFormed (i + 1) rest

def Join (x y z : Summary) : Prop :=
  ∃ c u v : Nat,
    c + u = x.opens ∧
    c + v = y.closes ∧
    (u = 0 ∨ v = 0) ∧
    x.len + y.len = z.len ∧
    x.closes + v = z.closes ∧
    u + y.opens = z.opens

def GateValid (g : Gate) : Prop := Join g.left g.right g.result

def GatesValid : List Gate → Prop
  | [] => True
  | g :: rest => GateValid g ∧ GatesValid rest

def demoGrammar : List (List Atom) := [
  [],
  [.lit '('],
  [.lit ')'],
  [.ref 1, .ref 1],
  [.ref 2, .ref 2],
  [.ref 3, .ref 3],
  [.ref 4, .ref 4],
  [.ref 5, .ref 5],
  [.ref 6, .ref 6],
  [.ref 7, .ref 7],
  [.ref 8, .ref 8],
  [.ref 9, .ref 9],
  [.ref 10, .ref 10],
  [.ref 11, .ref 11],
  [.ref 12, .ref 12],
  [.ref 13, .ref 13],
  [.ref 14, .ref 14],
  [.ref 15, .ref 15],
  [.ref 16, .ref 16],
  [.ref 17, .ref 17],
  [.ref 18, .ref 18],
  [.ref 19, .ref 19],
  [.ref 20, .ref 20],
  [.ref 21, .ref 21],
  [.ref 22, .ref 22],
  [.ref 23, .ref 23],
  [.ref 24, .ref 24],
  [.ref 25, .ref 25],
  [.ref 26, .ref 26],
  [.ref 27, .ref 27],
  [.ref 28, .ref 28],
  [.ref 29, .ref 29],
  [.ref 30, .ref 30],
  [.ref 31, .ref 31],
  [.ref 32, .ref 32],
  [.ref 33, .ref 33],
  [.ref 34, .ref 34],
  [.ref 35, .ref 35],
  [.ref 36, .ref 36],
  [.ref 37, .ref 37],
  [.ref 38, .ref 38],
  [.ref 39, .ref 39],
  [.ref 40, .ref 40],
  [.ref 41, .ref 41],
  [.ref 42, .ref 42],
  [.ref 43, .ref 43],
  [.ref 44, .ref 44],
  [.ref 45, .ref 45],
  [.ref 46, .ref 46],
  [.ref 47, .ref 47],
  [.ref 48, .ref 48],
  [.ref 49, .ref 49],
  [.ref 50, .ref 50],
  [.ref 51, .ref 51],
  [.ref 52, .ref 52],
  [.ref 53, .ref 53],
  [.ref 54, .ref 54],
  [.ref 55, .ref 55],
  [.ref 56, .ref 56],
  [.ref 57, .ref 57],
  [.ref 58, .ref 58],
  [.ref 59, .ref 59],
  [.ref 60, .ref 60],
  [.ref 61, .ref 61],
  [.ref 62, .ref 62],
  [.ref 63, .ref 63],
  [.ref 64, .ref 64],
  [.ref 65, .ref 65],
  [.ref 66, .ref 66],
  [.ref 67, .ref 67],
  [.ref 68, .ref 68],
  [.ref 69, .ref 69],
  [.ref 70, .ref 70],
  [.ref 71, .ref 71],
  [.ref 72, .ref 72],
  [.ref 73, .ref 73],
  [.ref 74, .ref 74],
  [.ref 75, .ref 75],
  [.ref 76, .ref 76],
  [.ref 77, .ref 77],
  [.ref 78, .ref 78],
  [.ref 79, .ref 79],
  [.ref 80, .ref 80],
  [.ref 81, .ref 81],
  [.ref 82, .ref 82],
  [.ref 83, .ref 83],
  [.ref 84, .ref 84],
  [.ref 85, .ref 85],
  [.ref 86, .ref 86],
  [.ref 87, .ref 87],
  [.ref 88, .ref 88],
  [.ref 89, .ref 89],
  [.ref 90, .ref 90],
  [.ref 91, .ref 91],
  [.ref 92, .ref 92],
  [.ref 93, .ref 93],
  [.ref 94, .ref 94],
  [.ref 95, .ref 95],
  [.ref 96, .ref 96],
  [.ref 97, .ref 97],
  [.ref 98, .ref 98],
  [.ref 99, .ref 99],
  [.ref 100, .ref 100],
  [.ref 101, .ref 101],
  [.ref 102, .ref 102],
  [.ref 103, .ref 103],
  [.ref 104, .ref 104],
  [.ref 105, .ref 105],
  [.ref 106, .ref 106],
  [.ref 107, .ref 107],
  [.ref 108, .ref 108],
  [.ref 109, .ref 109],
  [.ref 110, .ref 110],
  [.ref 111, .ref 111],
  [.ref 112, .ref 112],
  [.ref 113, .ref 113],
  [.ref 114, .ref 114],
  [.ref 115, .ref 115],
  [.ref 116, .ref 116],
  [.ref 117, .ref 117],
  [.ref 118, .ref 118],
  [.ref 119, .ref 119],
  [.ref 120, .ref 120],
  [.ref 121, .ref 121],
  [.ref 122, .ref 122],
  [.ref 123, .ref 123],
  [.ref 124, .ref 124],
  [.ref 125, .ref 125],
  [.ref 126, .ref 126],
  [.ref 127, .ref 127],
  [.ref 128, .ref 128],
  [.ref 129, .ref 129],
  [.ref 130, .ref 130],
  [.ref 131, .ref 131],
  [.ref 132, .ref 132],
  [.ref 133, .ref 133],
  [.ref 134, .ref 134],
  [.ref 135, .ref 135],
  [.ref 136, .ref 136],
  [.ref 137, .ref 137],
  [.ref 138, .ref 138],
  [.ref 139, .ref 139],
  [.ref 140, .ref 140],
  [.ref 141, .ref 141],
  [.ref 142, .ref 142],
  [.ref 143, .ref 143],
  [.ref 144, .ref 144],
  [.ref 145, .ref 145],
  [.ref 146, .ref 146],
  [.ref 147, .ref 147],
  [.ref 148, .ref 148],
  [.ref 149, .ref 149],
  [.ref 150, .ref 150],
  [.ref 151, .ref 151],
  [.ref 152, .ref 152],
  [.ref 153, .ref 153],
  [.ref 154, .ref 154],
  [.ref 155, .ref 155],
  [.ref 156, .ref 156],
  [.ref 157, .ref 157],
  [.ref 158, .ref 158],
  [.ref 159, .ref 159],
  [.ref 160, .ref 160],
  [.ref 161, .ref 161],
  [.ref 162, .ref 162],
  [.ref 163, .ref 163],
  [.ref 164, .ref 164],
  [.ref 165, .ref 165],
  [.ref 166, .ref 166],
  [.ref 167, .ref 167],
  [.ref 168, .ref 168],
  [.ref 169, .ref 169],
  [.ref 170, .ref 170],
  [.ref 171, .ref 171],
  [.ref 172, .ref 172],
  [.ref 173, .ref 173],
  [.ref 174, .ref 174],
  [.ref 175, .ref 175],
  [.ref 176, .ref 176],
  [.ref 177, .ref 177],
  [.ref 178, .ref 178],
  [.ref 179, .ref 179],
  [.ref 180, .ref 180],
  [.ref 181, .ref 181],
  [.ref 182, .ref 182],
  [.ref 183, .ref 183],
  [.ref 184, .ref 184],
  [.ref 185, .ref 185],
  [.ref 186, .ref 186],
  [.ref 187, .ref 187],
  [.ref 188, .ref 188],
  [.ref 189, .ref 189],
  [.ref 190, .ref 190],
  [.ref 191, .ref 191],
  [.ref 192, .ref 192],
  [.ref 193, .ref 193],
  [.ref 194, .ref 194],
  [.ref 195, .ref 195],
  [.ref 196, .ref 196],
  [.ref 197, .ref 197],
  [.ref 198, .ref 198],
  [.ref 199, .ref 199],
  [.ref 200, .ref 200],
  [.ref 0, .ref 201, .lit 'x', .ref 202, .ref 0],
]

def checkedSummaryTable : List Summary := [
  ⟨0, 0, 0⟩,
  ⟨1, 0, 1⟩,
  ⟨1, 1, 0⟩,
  ⟨2, 0, 2⟩,
  ⟨2, 2, 0⟩,
  ⟨4, 0, 4⟩,
  ⟨4, 4, 0⟩,
  ⟨8, 0, 8⟩,
  ⟨8, 8, 0⟩,
  ⟨16, 0, 16⟩,
  ⟨16, 16, 0⟩,
  ⟨32, 0, 32⟩,
  ⟨32, 32, 0⟩,
  ⟨64, 0, 64⟩,
  ⟨64, 64, 0⟩,
  ⟨128, 0, 128⟩,
  ⟨128, 128, 0⟩,
  ⟨256, 0, 256⟩,
  ⟨256, 256, 0⟩,
  ⟨512, 0, 512⟩,
  ⟨512, 512, 0⟩,
  ⟨1024, 0, 1024⟩,
  ⟨1024, 1024, 0⟩,
  ⟨2048, 0, 2048⟩,
  ⟨2048, 2048, 0⟩,
  ⟨4096, 0, 4096⟩,
  ⟨4096, 4096, 0⟩,
  ⟨8192, 0, 8192⟩,
  ⟨8192, 8192, 0⟩,
  ⟨16384, 0, 16384⟩,
  ⟨16384, 16384, 0⟩,
  ⟨32768, 0, 32768⟩,
  ⟨32768, 32768, 0⟩,
  ⟨65536, 0, 65536⟩,
  ⟨65536, 65536, 0⟩,
  ⟨131072, 0, 131072⟩,
  ⟨131072, 131072, 0⟩,
  ⟨262144, 0, 262144⟩,
  ⟨262144, 262144, 0⟩,
  ⟨524288, 0, 524288⟩,
  ⟨524288, 524288, 0⟩,
  ⟨1048576, 0, 1048576⟩,
  ⟨1048576, 1048576, 0⟩,
  ⟨2097152, 0, 2097152⟩,
  ⟨2097152, 2097152, 0⟩,
  ⟨4194304, 0, 4194304⟩,
  ⟨4194304, 4194304, 0⟩,
  ⟨8388608, 0, 8388608⟩,
  ⟨8388608, 8388608, 0⟩,
  ⟨16777216, 0, 16777216⟩,
  ⟨16777216, 16777216, 0⟩,
  ⟨33554432, 0, 33554432⟩,
  ⟨33554432, 33554432, 0⟩,
  ⟨67108864, 0, 67108864⟩,
  ⟨67108864, 67108864, 0⟩,
  ⟨134217728, 0, 134217728⟩,
  ⟨134217728, 134217728, 0⟩,
  ⟨268435456, 0, 268435456⟩,
  ⟨268435456, 268435456, 0⟩,
  ⟨536870912, 0, 536870912⟩,
  ⟨536870912, 536870912, 0⟩,
  ⟨1073741824, 0, 1073741824⟩,
  ⟨1073741824, 1073741824, 0⟩,
  ⟨2147483648, 0, 2147483648⟩,
  ⟨2147483648, 2147483648, 0⟩,
  ⟨4294967296, 0, 4294967296⟩,
  ⟨4294967296, 4294967296, 0⟩,
  ⟨8589934592, 0, 8589934592⟩,
  ⟨8589934592, 8589934592, 0⟩,
  ⟨17179869184, 0, 17179869184⟩,
  ⟨17179869184, 17179869184, 0⟩,
  ⟨34359738368, 0, 34359738368⟩,
  ⟨34359738368, 34359738368, 0⟩,
  ⟨68719476736, 0, 68719476736⟩,
  ⟨68719476736, 68719476736, 0⟩,
  ⟨137438953472, 0, 137438953472⟩,
  ⟨137438953472, 137438953472, 0⟩,
  ⟨274877906944, 0, 274877906944⟩,
  ⟨274877906944, 274877906944, 0⟩,
  ⟨549755813888, 0, 549755813888⟩,
  ⟨549755813888, 549755813888, 0⟩,
  ⟨1099511627776, 0, 1099511627776⟩,
  ⟨1099511627776, 1099511627776, 0⟩,
  ⟨2199023255552, 0, 2199023255552⟩,
  ⟨2199023255552, 2199023255552, 0⟩,
  ⟨4398046511104, 0, 4398046511104⟩,
  ⟨4398046511104, 4398046511104, 0⟩,
  ⟨8796093022208, 0, 8796093022208⟩,
  ⟨8796093022208, 8796093022208, 0⟩,
  ⟨17592186044416, 0, 17592186044416⟩,
  ⟨17592186044416, 17592186044416, 0⟩,
  ⟨35184372088832, 0, 35184372088832⟩,
  ⟨35184372088832, 35184372088832, 0⟩,
  ⟨70368744177664, 0, 70368744177664⟩,
  ⟨70368744177664, 70368744177664, 0⟩,
  ⟨140737488355328, 0, 140737488355328⟩,
  ⟨140737488355328, 140737488355328, 0⟩,
  ⟨281474976710656, 0, 281474976710656⟩,
  ⟨281474976710656, 281474976710656, 0⟩,
  ⟨562949953421312, 0, 562949953421312⟩,
  ⟨562949953421312, 562949953421312, 0⟩,
  ⟨1125899906842624, 0, 1125899906842624⟩,
  ⟨1125899906842624, 1125899906842624, 0⟩,
  ⟨2251799813685248, 0, 2251799813685248⟩,
  ⟨2251799813685248, 2251799813685248, 0⟩,
  ⟨4503599627370496, 0, 4503599627370496⟩,
  ⟨4503599627370496, 4503599627370496, 0⟩,
  ⟨9007199254740992, 0, 9007199254740992⟩,
  ⟨9007199254740992, 9007199254740992, 0⟩,
  ⟨18014398509481984, 0, 18014398509481984⟩,
  ⟨18014398509481984, 18014398509481984, 0⟩,
  ⟨36028797018963968, 0, 36028797018963968⟩,
  ⟨36028797018963968, 36028797018963968, 0⟩,
  ⟨72057594037927936, 0, 72057594037927936⟩,
  ⟨72057594037927936, 72057594037927936, 0⟩,
  ⟨144115188075855872, 0, 144115188075855872⟩,
  ⟨144115188075855872, 144115188075855872, 0⟩,
  ⟨288230376151711744, 0, 288230376151711744⟩,
  ⟨288230376151711744, 288230376151711744, 0⟩,
  ⟨576460752303423488, 0, 576460752303423488⟩,
  ⟨576460752303423488, 576460752303423488, 0⟩,
  ⟨1152921504606846976, 0, 1152921504606846976⟩,
  ⟨1152921504606846976, 1152921504606846976, 0⟩,
  ⟨2305843009213693952, 0, 2305843009213693952⟩,
  ⟨2305843009213693952, 2305843009213693952, 0⟩,
  ⟨4611686018427387904, 0, 4611686018427387904⟩,
  ⟨4611686018427387904, 4611686018427387904, 0⟩,
  ⟨9223372036854775808, 0, 9223372036854775808⟩,
  ⟨9223372036854775808, 9223372036854775808, 0⟩,
  ⟨18446744073709551616, 0, 18446744073709551616⟩,
  ⟨18446744073709551616, 18446744073709551616, 0⟩,
  ⟨36893488147419103232, 0, 36893488147419103232⟩,
  ⟨36893488147419103232, 36893488147419103232, 0⟩,
  ⟨73786976294838206464, 0, 73786976294838206464⟩,
  ⟨73786976294838206464, 73786976294838206464, 0⟩,
  ⟨147573952589676412928, 0, 147573952589676412928⟩,
  ⟨147573952589676412928, 147573952589676412928, 0⟩,
  ⟨295147905179352825856, 0, 295147905179352825856⟩,
  ⟨295147905179352825856, 295147905179352825856, 0⟩,
  ⟨590295810358705651712, 0, 590295810358705651712⟩,
  ⟨590295810358705651712, 590295810358705651712, 0⟩,
  ⟨1180591620717411303424, 0, 1180591620717411303424⟩,
  ⟨1180591620717411303424, 1180591620717411303424, 0⟩,
  ⟨2361183241434822606848, 0, 2361183241434822606848⟩,
  ⟨2361183241434822606848, 2361183241434822606848, 0⟩,
  ⟨4722366482869645213696, 0, 4722366482869645213696⟩,
  ⟨4722366482869645213696, 4722366482869645213696, 0⟩,
  ⟨9444732965739290427392, 0, 9444732965739290427392⟩,
  ⟨9444732965739290427392, 9444732965739290427392, 0⟩,
  ⟨18889465931478580854784, 0, 18889465931478580854784⟩,
  ⟨18889465931478580854784, 18889465931478580854784, 0⟩,
  ⟨37778931862957161709568, 0, 37778931862957161709568⟩,
  ⟨37778931862957161709568, 37778931862957161709568, 0⟩,
  ⟨75557863725914323419136, 0, 75557863725914323419136⟩,
  ⟨75557863725914323419136, 75557863725914323419136, 0⟩,
  ⟨151115727451828646838272, 0, 151115727451828646838272⟩,
  ⟨151115727451828646838272, 151115727451828646838272, 0⟩,
  ⟨302231454903657293676544, 0, 302231454903657293676544⟩,
  ⟨302231454903657293676544, 302231454903657293676544, 0⟩,
  ⟨604462909807314587353088, 0, 604462909807314587353088⟩,
  ⟨604462909807314587353088, 604462909807314587353088, 0⟩,
  ⟨1208925819614629174706176, 0, 1208925819614629174706176⟩,
  ⟨1208925819614629174706176, 1208925819614629174706176, 0⟩,
  ⟨2417851639229258349412352, 0, 2417851639229258349412352⟩,
  ⟨2417851639229258349412352, 2417851639229258349412352, 0⟩,
  ⟨4835703278458516698824704, 0, 4835703278458516698824704⟩,
  ⟨4835703278458516698824704, 4835703278458516698824704, 0⟩,
  ⟨9671406556917033397649408, 0, 9671406556917033397649408⟩,
  ⟨9671406556917033397649408, 9671406556917033397649408, 0⟩,
  ⟨19342813113834066795298816, 0, 19342813113834066795298816⟩,
  ⟨19342813113834066795298816, 19342813113834066795298816, 0⟩,
  ⟨38685626227668133590597632, 0, 38685626227668133590597632⟩,
  ⟨38685626227668133590597632, 38685626227668133590597632, 0⟩,
  ⟨77371252455336267181195264, 0, 77371252455336267181195264⟩,
  ⟨77371252455336267181195264, 77371252455336267181195264, 0⟩,
  ⟨154742504910672534362390528, 0, 154742504910672534362390528⟩,
  ⟨154742504910672534362390528, 154742504910672534362390528, 0⟩,
  ⟨309485009821345068724781056, 0, 309485009821345068724781056⟩,
  ⟨309485009821345068724781056, 309485009821345068724781056, 0⟩,
  ⟨618970019642690137449562112, 0, 618970019642690137449562112⟩,
  ⟨618970019642690137449562112, 618970019642690137449562112, 0⟩,
  ⟨1237940039285380274899124224, 0, 1237940039285380274899124224⟩,
  ⟨1237940039285380274899124224, 1237940039285380274899124224, 0⟩,
  ⟨2475880078570760549798248448, 0, 2475880078570760549798248448⟩,
  ⟨2475880078570760549798248448, 2475880078570760549798248448, 0⟩,
  ⟨4951760157141521099596496896, 0, 4951760157141521099596496896⟩,
  ⟨4951760157141521099596496896, 4951760157141521099596496896, 0⟩,
  ⟨9903520314283042199192993792, 0, 9903520314283042199192993792⟩,
  ⟨9903520314283042199192993792, 9903520314283042199192993792, 0⟩,
  ⟨19807040628566084398385987584, 0, 19807040628566084398385987584⟩,
  ⟨19807040628566084398385987584, 19807040628566084398385987584, 0⟩,
  ⟨39614081257132168796771975168, 0, 39614081257132168796771975168⟩,
  ⟨39614081257132168796771975168, 39614081257132168796771975168, 0⟩,
  ⟨79228162514264337593543950336, 0, 79228162514264337593543950336⟩,
  ⟨79228162514264337593543950336, 79228162514264337593543950336, 0⟩,
  ⟨158456325028528675187087900672, 0, 158456325028528675187087900672⟩,
  ⟨158456325028528675187087900672, 158456325028528675187087900672, 0⟩,
  ⟨316912650057057350374175801344, 0, 316912650057057350374175801344⟩,
  ⟨316912650057057350374175801344, 316912650057057350374175801344, 0⟩,
  ⟨633825300114114700748351602688, 0, 633825300114114700748351602688⟩,
  ⟨633825300114114700748351602688, 633825300114114700748351602688, 0⟩,
  ⟨1267650600228229401496703205376, 0, 1267650600228229401496703205376⟩,
  ⟨1267650600228229401496703205376, 1267650600228229401496703205376, 0⟩,
  ⟨2535301200456458802993406410753, 0, 0⟩,
]

def computedSummaryTable : List Summary := summarizeRules demoGrammar []

def computedGateList : List Gate := buildGates demoGrammar []

theorem grammar_is_well_formed : grammarWellFormed 0 demoGrammar = true := by decide

theorem computed_table_matches_certificate : computedSummaryTable = checkedSummaryTable := by decide

theorem root_summary_is_balanced_length_2_pow_101_plus_1 :
    computedSummaryTable.getLast? = some ⟨2535301200456458802993406410753, 0, 0⟩ := by decide

theorem binary_length_identity : 2 ^ 101 + 1 = 2535301200456458802993406410753 := by decide

theorem gate_count_is_407 : computedGateList.length = 407 := by decide

def checkedGate0000 : Gate := ⟨⟨0, 0, 0⟩, ⟨1, 0, 1⟩, ⟨1, 0, 1⟩⟩
theorem checkedGate0000_join : GateValid checkedGate0000 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0001 : Gate := ⟨⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨1, 1, 0⟩⟩
theorem checkedGate0001_join : GateValid checkedGate0001 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1 (by decide)))

def checkedGate0002 : Gate := ⟨⟨0, 0, 0⟩, ⟨1, 0, 1⟩, ⟨1, 0, 1⟩⟩
theorem checkedGate0002_join : GateValid checkedGate0002 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0003 : Gate := ⟨⟨1, 0, 1⟩, ⟨1, 0, 1⟩, ⟨2, 0, 2⟩⟩
theorem checkedGate0003_join : GateValid checkedGate0003 := by
  exact Exists.intro 0 (Exists.intro 1 (Exists.intro 0 (by decide)))

def checkedGate0004 : Gate := ⟨⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨1, 1, 0⟩⟩
theorem checkedGate0004_join : GateValid checkedGate0004 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1 (by decide)))

def checkedGate0005 : Gate := ⟨⟨1, 1, 0⟩, ⟨1, 1, 0⟩, ⟨2, 2, 0⟩⟩
theorem checkedGate0005_join : GateValid checkedGate0005 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1 (by decide)))

def checkedGate0006 : Gate := ⟨⟨0, 0, 0⟩, ⟨2, 0, 2⟩, ⟨2, 0, 2⟩⟩
theorem checkedGate0006_join : GateValid checkedGate0006 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0007 : Gate := ⟨⟨2, 0, 2⟩, ⟨2, 0, 2⟩, ⟨4, 0, 4⟩⟩
theorem checkedGate0007_join : GateValid checkedGate0007 := by
  exact Exists.intro 0 (Exists.intro 2 (Exists.intro 0 (by decide)))

def checkedGate0008 : Gate := ⟨⟨0, 0, 0⟩, ⟨2, 2, 0⟩, ⟨2, 2, 0⟩⟩
theorem checkedGate0008_join : GateValid checkedGate0008 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2 (by decide)))

def checkedGate0009 : Gate := ⟨⟨2, 2, 0⟩, ⟨2, 2, 0⟩, ⟨4, 4, 0⟩⟩
theorem checkedGate0009_join : GateValid checkedGate0009 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2 (by decide)))

def checkedGate0010 : Gate := ⟨⟨0, 0, 0⟩, ⟨4, 0, 4⟩, ⟨4, 0, 4⟩⟩
theorem checkedGate0010_join : GateValid checkedGate0010 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0011 : Gate := ⟨⟨4, 0, 4⟩, ⟨4, 0, 4⟩, ⟨8, 0, 8⟩⟩
theorem checkedGate0011_join : GateValid checkedGate0011 := by
  exact Exists.intro 0 (Exists.intro 4 (Exists.intro 0 (by decide)))

def checkedGate0012 : Gate := ⟨⟨0, 0, 0⟩, ⟨4, 4, 0⟩, ⟨4, 4, 0⟩⟩
theorem checkedGate0012_join : GateValid checkedGate0012 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4 (by decide)))

def checkedGate0013 : Gate := ⟨⟨4, 4, 0⟩, ⟨4, 4, 0⟩, ⟨8, 8, 0⟩⟩
theorem checkedGate0013_join : GateValid checkedGate0013 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4 (by decide)))

def checkedGate0014 : Gate := ⟨⟨0, 0, 0⟩, ⟨8, 0, 8⟩, ⟨8, 0, 8⟩⟩
theorem checkedGate0014_join : GateValid checkedGate0014 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0015 : Gate := ⟨⟨8, 0, 8⟩, ⟨8, 0, 8⟩, ⟨16, 0, 16⟩⟩
theorem checkedGate0015_join : GateValid checkedGate0015 := by
  exact Exists.intro 0 (Exists.intro 8 (Exists.intro 0 (by decide)))

def checkedGate0016 : Gate := ⟨⟨0, 0, 0⟩, ⟨8, 8, 0⟩, ⟨8, 8, 0⟩⟩
theorem checkedGate0016_join : GateValid checkedGate0016 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 8 (by decide)))

def checkedGate0017 : Gate := ⟨⟨8, 8, 0⟩, ⟨8, 8, 0⟩, ⟨16, 16, 0⟩⟩
theorem checkedGate0017_join : GateValid checkedGate0017 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 8 (by decide)))

def checkedGate0018 : Gate := ⟨⟨0, 0, 0⟩, ⟨16, 0, 16⟩, ⟨16, 0, 16⟩⟩
theorem checkedGate0018_join : GateValid checkedGate0018 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0019 : Gate := ⟨⟨16, 0, 16⟩, ⟨16, 0, 16⟩, ⟨32, 0, 32⟩⟩
theorem checkedGate0019_join : GateValid checkedGate0019 := by
  exact Exists.intro 0 (Exists.intro 16 (Exists.intro 0 (by decide)))

def checkedGate0020 : Gate := ⟨⟨0, 0, 0⟩, ⟨16, 16, 0⟩, ⟨16, 16, 0⟩⟩
theorem checkedGate0020_join : GateValid checkedGate0020 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 16 (by decide)))

def checkedGate0021 : Gate := ⟨⟨16, 16, 0⟩, ⟨16, 16, 0⟩, ⟨32, 32, 0⟩⟩
theorem checkedGate0021_join : GateValid checkedGate0021 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 16 (by decide)))

def checkedGate0022 : Gate := ⟨⟨0, 0, 0⟩, ⟨32, 0, 32⟩, ⟨32, 0, 32⟩⟩
theorem checkedGate0022_join : GateValid checkedGate0022 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0023 : Gate := ⟨⟨32, 0, 32⟩, ⟨32, 0, 32⟩, ⟨64, 0, 64⟩⟩
theorem checkedGate0023_join : GateValid checkedGate0023 := by
  exact Exists.intro 0 (Exists.intro 32 (Exists.intro 0 (by decide)))

def checkedGate0024 : Gate := ⟨⟨0, 0, 0⟩, ⟨32, 32, 0⟩, ⟨32, 32, 0⟩⟩
theorem checkedGate0024_join : GateValid checkedGate0024 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 32 (by decide)))

def checkedGate0025 : Gate := ⟨⟨32, 32, 0⟩, ⟨32, 32, 0⟩, ⟨64, 64, 0⟩⟩
theorem checkedGate0025_join : GateValid checkedGate0025 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 32 (by decide)))

def checkedGate0026 : Gate := ⟨⟨0, 0, 0⟩, ⟨64, 0, 64⟩, ⟨64, 0, 64⟩⟩
theorem checkedGate0026_join : GateValid checkedGate0026 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0027 : Gate := ⟨⟨64, 0, 64⟩, ⟨64, 0, 64⟩, ⟨128, 0, 128⟩⟩
theorem checkedGate0027_join : GateValid checkedGate0027 := by
  exact Exists.intro 0 (Exists.intro 64 (Exists.intro 0 (by decide)))

def checkedGate0028 : Gate := ⟨⟨0, 0, 0⟩, ⟨64, 64, 0⟩, ⟨64, 64, 0⟩⟩
theorem checkedGate0028_join : GateValid checkedGate0028 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 64 (by decide)))

def checkedGate0029 : Gate := ⟨⟨64, 64, 0⟩, ⟨64, 64, 0⟩, ⟨128, 128, 0⟩⟩
theorem checkedGate0029_join : GateValid checkedGate0029 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 64 (by decide)))

def checkedGate0030 : Gate := ⟨⟨0, 0, 0⟩, ⟨128, 0, 128⟩, ⟨128, 0, 128⟩⟩
theorem checkedGate0030_join : GateValid checkedGate0030 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0031 : Gate := ⟨⟨128, 0, 128⟩, ⟨128, 0, 128⟩, ⟨256, 0, 256⟩⟩
theorem checkedGate0031_join : GateValid checkedGate0031 := by
  exact Exists.intro 0 (Exists.intro 128 (Exists.intro 0 (by decide)))

def checkedGate0032 : Gate := ⟨⟨0, 0, 0⟩, ⟨128, 128, 0⟩, ⟨128, 128, 0⟩⟩
theorem checkedGate0032_join : GateValid checkedGate0032 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 128 (by decide)))

def checkedGate0033 : Gate := ⟨⟨128, 128, 0⟩, ⟨128, 128, 0⟩, ⟨256, 256, 0⟩⟩
theorem checkedGate0033_join : GateValid checkedGate0033 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 128 (by decide)))

def checkedGate0034 : Gate := ⟨⟨0, 0, 0⟩, ⟨256, 0, 256⟩, ⟨256, 0, 256⟩⟩
theorem checkedGate0034_join : GateValid checkedGate0034 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0035 : Gate := ⟨⟨256, 0, 256⟩, ⟨256, 0, 256⟩, ⟨512, 0, 512⟩⟩
theorem checkedGate0035_join : GateValid checkedGate0035 := by
  exact Exists.intro 0 (Exists.intro 256 (Exists.intro 0 (by decide)))

def checkedGate0036 : Gate := ⟨⟨0, 0, 0⟩, ⟨256, 256, 0⟩, ⟨256, 256, 0⟩⟩
theorem checkedGate0036_join : GateValid checkedGate0036 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 256 (by decide)))

def checkedGate0037 : Gate := ⟨⟨256, 256, 0⟩, ⟨256, 256, 0⟩, ⟨512, 512, 0⟩⟩
theorem checkedGate0037_join : GateValid checkedGate0037 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 256 (by decide)))

def checkedGate0038 : Gate := ⟨⟨0, 0, 0⟩, ⟨512, 0, 512⟩, ⟨512, 0, 512⟩⟩
theorem checkedGate0038_join : GateValid checkedGate0038 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0039 : Gate := ⟨⟨512, 0, 512⟩, ⟨512, 0, 512⟩, ⟨1024, 0, 1024⟩⟩
theorem checkedGate0039_join : GateValid checkedGate0039 := by
  exact Exists.intro 0 (Exists.intro 512 (Exists.intro 0 (by decide)))

def checkedGate0040 : Gate := ⟨⟨0, 0, 0⟩, ⟨512, 512, 0⟩, ⟨512, 512, 0⟩⟩
theorem checkedGate0040_join : GateValid checkedGate0040 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 512 (by decide)))

def checkedGate0041 : Gate := ⟨⟨512, 512, 0⟩, ⟨512, 512, 0⟩, ⟨1024, 1024, 0⟩⟩
theorem checkedGate0041_join : GateValid checkedGate0041 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 512 (by decide)))

def checkedGate0042 : Gate := ⟨⟨0, 0, 0⟩, ⟨1024, 0, 1024⟩, ⟨1024, 0, 1024⟩⟩
theorem checkedGate0042_join : GateValid checkedGate0042 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0043 : Gate := ⟨⟨1024, 0, 1024⟩, ⟨1024, 0, 1024⟩, ⟨2048, 0, 2048⟩⟩
theorem checkedGate0043_join : GateValid checkedGate0043 := by
  exact Exists.intro 0 (Exists.intro 1024 (Exists.intro 0 (by decide)))

def checkedGate0044 : Gate := ⟨⟨0, 0, 0⟩, ⟨1024, 1024, 0⟩, ⟨1024, 1024, 0⟩⟩
theorem checkedGate0044_join : GateValid checkedGate0044 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1024 (by decide)))

def checkedGate0045 : Gate := ⟨⟨1024, 1024, 0⟩, ⟨1024, 1024, 0⟩, ⟨2048, 2048, 0⟩⟩
theorem checkedGate0045_join : GateValid checkedGate0045 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1024 (by decide)))

def checkedGate0046 : Gate := ⟨⟨0, 0, 0⟩, ⟨2048, 0, 2048⟩, ⟨2048, 0, 2048⟩⟩
theorem checkedGate0046_join : GateValid checkedGate0046 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0047 : Gate := ⟨⟨2048, 0, 2048⟩, ⟨2048, 0, 2048⟩, ⟨4096, 0, 4096⟩⟩
theorem checkedGate0047_join : GateValid checkedGate0047 := by
  exact Exists.intro 0 (Exists.intro 2048 (Exists.intro 0 (by decide)))

def checkedGate0048 : Gate := ⟨⟨0, 0, 0⟩, ⟨2048, 2048, 0⟩, ⟨2048, 2048, 0⟩⟩
theorem checkedGate0048_join : GateValid checkedGate0048 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2048 (by decide)))

def checkedGate0049 : Gate := ⟨⟨2048, 2048, 0⟩, ⟨2048, 2048, 0⟩, ⟨4096, 4096, 0⟩⟩
theorem checkedGate0049_join : GateValid checkedGate0049 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2048 (by decide)))

def checkedGate0050 : Gate := ⟨⟨0, 0, 0⟩, ⟨4096, 0, 4096⟩, ⟨4096, 0, 4096⟩⟩
theorem checkedGate0050_join : GateValid checkedGate0050 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0051 : Gate := ⟨⟨4096, 0, 4096⟩, ⟨4096, 0, 4096⟩, ⟨8192, 0, 8192⟩⟩
theorem checkedGate0051_join : GateValid checkedGate0051 := by
  exact Exists.intro 0 (Exists.intro 4096 (Exists.intro 0 (by decide)))

def checkedGate0052 : Gate := ⟨⟨0, 0, 0⟩, ⟨4096, 4096, 0⟩, ⟨4096, 4096, 0⟩⟩
theorem checkedGate0052_join : GateValid checkedGate0052 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4096 (by decide)))

def checkedGate0053 : Gate := ⟨⟨4096, 4096, 0⟩, ⟨4096, 4096, 0⟩, ⟨8192, 8192, 0⟩⟩
theorem checkedGate0053_join : GateValid checkedGate0053 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4096 (by decide)))

def checkedGate0054 : Gate := ⟨⟨0, 0, 0⟩, ⟨8192, 0, 8192⟩, ⟨8192, 0, 8192⟩⟩
theorem checkedGate0054_join : GateValid checkedGate0054 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0055 : Gate := ⟨⟨8192, 0, 8192⟩, ⟨8192, 0, 8192⟩, ⟨16384, 0, 16384⟩⟩
theorem checkedGate0055_join : GateValid checkedGate0055 := by
  exact Exists.intro 0 (Exists.intro 8192 (Exists.intro 0 (by decide)))

def checkedGate0056 : Gate := ⟨⟨0, 0, 0⟩, ⟨8192, 8192, 0⟩, ⟨8192, 8192, 0⟩⟩
theorem checkedGate0056_join : GateValid checkedGate0056 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 8192 (by decide)))

def checkedGate0057 : Gate := ⟨⟨8192, 8192, 0⟩, ⟨8192, 8192, 0⟩, ⟨16384, 16384, 0⟩⟩
theorem checkedGate0057_join : GateValid checkedGate0057 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 8192 (by decide)))

def checkedGate0058 : Gate := ⟨⟨0, 0, 0⟩, ⟨16384, 0, 16384⟩, ⟨16384, 0, 16384⟩⟩
theorem checkedGate0058_join : GateValid checkedGate0058 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0059 : Gate := ⟨⟨16384, 0, 16384⟩, ⟨16384, 0, 16384⟩, ⟨32768, 0, 32768⟩⟩
theorem checkedGate0059_join : GateValid checkedGate0059 := by
  exact Exists.intro 0 (Exists.intro 16384 (Exists.intro 0 (by decide)))

def checkedGate0060 : Gate := ⟨⟨0, 0, 0⟩, ⟨16384, 16384, 0⟩, ⟨16384, 16384, 0⟩⟩
theorem checkedGate0060_join : GateValid checkedGate0060 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 16384 (by decide)))

def checkedGate0061 : Gate := ⟨⟨16384, 16384, 0⟩, ⟨16384, 16384, 0⟩, ⟨32768, 32768, 0⟩⟩
theorem checkedGate0061_join : GateValid checkedGate0061 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 16384 (by decide)))

def checkedGate0062 : Gate := ⟨⟨0, 0, 0⟩, ⟨32768, 0, 32768⟩, ⟨32768, 0, 32768⟩⟩
theorem checkedGate0062_join : GateValid checkedGate0062 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0063 : Gate := ⟨⟨32768, 0, 32768⟩, ⟨32768, 0, 32768⟩, ⟨65536, 0, 65536⟩⟩
theorem checkedGate0063_join : GateValid checkedGate0063 := by
  exact Exists.intro 0 (Exists.intro 32768 (Exists.intro 0 (by decide)))

def checkedGate0064 : Gate := ⟨⟨0, 0, 0⟩, ⟨32768, 32768, 0⟩, ⟨32768, 32768, 0⟩⟩
theorem checkedGate0064_join : GateValid checkedGate0064 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 32768 (by decide)))

def checkedGate0065 : Gate := ⟨⟨32768, 32768, 0⟩, ⟨32768, 32768, 0⟩, ⟨65536, 65536, 0⟩⟩
theorem checkedGate0065_join : GateValid checkedGate0065 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 32768 (by decide)))

def checkedGate0066 : Gate := ⟨⟨0, 0, 0⟩, ⟨65536, 0, 65536⟩, ⟨65536, 0, 65536⟩⟩
theorem checkedGate0066_join : GateValid checkedGate0066 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0067 : Gate := ⟨⟨65536, 0, 65536⟩, ⟨65536, 0, 65536⟩, ⟨131072, 0, 131072⟩⟩
theorem checkedGate0067_join : GateValid checkedGate0067 := by
  exact Exists.intro 0 (Exists.intro 65536 (Exists.intro 0 (by decide)))

def checkedGate0068 : Gate := ⟨⟨0, 0, 0⟩, ⟨65536, 65536, 0⟩, ⟨65536, 65536, 0⟩⟩
theorem checkedGate0068_join : GateValid checkedGate0068 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 65536 (by decide)))

def checkedGate0069 : Gate := ⟨⟨65536, 65536, 0⟩, ⟨65536, 65536, 0⟩, ⟨131072, 131072, 0⟩⟩
theorem checkedGate0069_join : GateValid checkedGate0069 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 65536 (by decide)))

def checkedGate0070 : Gate := ⟨⟨0, 0, 0⟩, ⟨131072, 0, 131072⟩, ⟨131072, 0, 131072⟩⟩
theorem checkedGate0070_join : GateValid checkedGate0070 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0071 : Gate := ⟨⟨131072, 0, 131072⟩, ⟨131072, 0, 131072⟩, ⟨262144, 0, 262144⟩⟩
theorem checkedGate0071_join : GateValid checkedGate0071 := by
  exact Exists.intro 0 (Exists.intro 131072 (Exists.intro 0 (by decide)))

def checkedGate0072 : Gate := ⟨⟨0, 0, 0⟩, ⟨131072, 131072, 0⟩, ⟨131072, 131072, 0⟩⟩
theorem checkedGate0072_join : GateValid checkedGate0072 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 131072 (by decide)))

def checkedGate0073 : Gate := ⟨⟨131072, 131072, 0⟩, ⟨131072, 131072, 0⟩, ⟨262144, 262144, 0⟩⟩
theorem checkedGate0073_join : GateValid checkedGate0073 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 131072 (by decide)))

def checkedGate0074 : Gate := ⟨⟨0, 0, 0⟩, ⟨262144, 0, 262144⟩, ⟨262144, 0, 262144⟩⟩
theorem checkedGate0074_join : GateValid checkedGate0074 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0075 : Gate := ⟨⟨262144, 0, 262144⟩, ⟨262144, 0, 262144⟩, ⟨524288, 0, 524288⟩⟩
theorem checkedGate0075_join : GateValid checkedGate0075 := by
  exact Exists.intro 0 (Exists.intro 262144 (Exists.intro 0 (by decide)))

def checkedGate0076 : Gate := ⟨⟨0, 0, 0⟩, ⟨262144, 262144, 0⟩, ⟨262144, 262144, 0⟩⟩
theorem checkedGate0076_join : GateValid checkedGate0076 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 262144 (by decide)))

def checkedGate0077 : Gate := ⟨⟨262144, 262144, 0⟩, ⟨262144, 262144, 0⟩, ⟨524288, 524288, 0⟩⟩
theorem checkedGate0077_join : GateValid checkedGate0077 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 262144 (by decide)))

def checkedGate0078 : Gate := ⟨⟨0, 0, 0⟩, ⟨524288, 0, 524288⟩, ⟨524288, 0, 524288⟩⟩
theorem checkedGate0078_join : GateValid checkedGate0078 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0079 : Gate := ⟨⟨524288, 0, 524288⟩, ⟨524288, 0, 524288⟩, ⟨1048576, 0, 1048576⟩⟩
theorem checkedGate0079_join : GateValid checkedGate0079 := by
  exact Exists.intro 0 (Exists.intro 524288 (Exists.intro 0 (by decide)))

def checkedGate0080 : Gate := ⟨⟨0, 0, 0⟩, ⟨524288, 524288, 0⟩, ⟨524288, 524288, 0⟩⟩
theorem checkedGate0080_join : GateValid checkedGate0080 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 524288 (by decide)))

def checkedGate0081 : Gate := ⟨⟨524288, 524288, 0⟩, ⟨524288, 524288, 0⟩, ⟨1048576, 1048576, 0⟩⟩
theorem checkedGate0081_join : GateValid checkedGate0081 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 524288 (by decide)))

def checkedGate0082 : Gate := ⟨⟨0, 0, 0⟩, ⟨1048576, 0, 1048576⟩, ⟨1048576, 0, 1048576⟩⟩
theorem checkedGate0082_join : GateValid checkedGate0082 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0083 : Gate := ⟨⟨1048576, 0, 1048576⟩, ⟨1048576, 0, 1048576⟩, ⟨2097152, 0, 2097152⟩⟩
theorem checkedGate0083_join : GateValid checkedGate0083 := by
  exact Exists.intro 0 (Exists.intro 1048576 (Exists.intro 0 (by decide)))

def checkedGate0084 : Gate := ⟨⟨0, 0, 0⟩, ⟨1048576, 1048576, 0⟩, ⟨1048576, 1048576, 0⟩⟩
theorem checkedGate0084_join : GateValid checkedGate0084 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1048576 (by decide)))

def checkedGate0085 : Gate := ⟨⟨1048576, 1048576, 0⟩, ⟨1048576, 1048576, 0⟩, ⟨2097152, 2097152, 0⟩⟩
theorem checkedGate0085_join : GateValid checkedGate0085 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1048576 (by decide)))

def checkedGate0086 : Gate := ⟨⟨0, 0, 0⟩, ⟨2097152, 0, 2097152⟩, ⟨2097152, 0, 2097152⟩⟩
theorem checkedGate0086_join : GateValid checkedGate0086 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0087 : Gate := ⟨⟨2097152, 0, 2097152⟩, ⟨2097152, 0, 2097152⟩, ⟨4194304, 0, 4194304⟩⟩
theorem checkedGate0087_join : GateValid checkedGate0087 := by
  exact Exists.intro 0 (Exists.intro 2097152 (Exists.intro 0 (by decide)))

def checkedGate0088 : Gate := ⟨⟨0, 0, 0⟩, ⟨2097152, 2097152, 0⟩, ⟨2097152, 2097152, 0⟩⟩
theorem checkedGate0088_join : GateValid checkedGate0088 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2097152 (by decide)))

def checkedGate0089 : Gate := ⟨⟨2097152, 2097152, 0⟩, ⟨2097152, 2097152, 0⟩, ⟨4194304, 4194304, 0⟩⟩
theorem checkedGate0089_join : GateValid checkedGate0089 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2097152 (by decide)))

def checkedGate0090 : Gate := ⟨⟨0, 0, 0⟩, ⟨4194304, 0, 4194304⟩, ⟨4194304, 0, 4194304⟩⟩
theorem checkedGate0090_join : GateValid checkedGate0090 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0091 : Gate := ⟨⟨4194304, 0, 4194304⟩, ⟨4194304, 0, 4194304⟩, ⟨8388608, 0, 8388608⟩⟩
theorem checkedGate0091_join : GateValid checkedGate0091 := by
  exact Exists.intro 0 (Exists.intro 4194304 (Exists.intro 0 (by decide)))

def checkedGate0092 : Gate := ⟨⟨0, 0, 0⟩, ⟨4194304, 4194304, 0⟩, ⟨4194304, 4194304, 0⟩⟩
theorem checkedGate0092_join : GateValid checkedGate0092 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4194304 (by decide)))

def checkedGate0093 : Gate := ⟨⟨4194304, 4194304, 0⟩, ⟨4194304, 4194304, 0⟩, ⟨8388608, 8388608, 0⟩⟩
theorem checkedGate0093_join : GateValid checkedGate0093 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4194304 (by decide)))

def checkedGate0094 : Gate := ⟨⟨0, 0, 0⟩, ⟨8388608, 0, 8388608⟩, ⟨8388608, 0, 8388608⟩⟩
theorem checkedGate0094_join : GateValid checkedGate0094 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0095 : Gate := ⟨⟨8388608, 0, 8388608⟩, ⟨8388608, 0, 8388608⟩, ⟨16777216, 0, 16777216⟩⟩
theorem checkedGate0095_join : GateValid checkedGate0095 := by
  exact Exists.intro 0 (Exists.intro 8388608 (Exists.intro 0 (by decide)))

def checkedGate0096 : Gate := ⟨⟨0, 0, 0⟩, ⟨8388608, 8388608, 0⟩, ⟨8388608, 8388608, 0⟩⟩
theorem checkedGate0096_join : GateValid checkedGate0096 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 8388608 (by decide)))

def checkedGate0097 : Gate := ⟨⟨8388608, 8388608, 0⟩, ⟨8388608, 8388608, 0⟩, ⟨16777216, 16777216, 0⟩⟩
theorem checkedGate0097_join : GateValid checkedGate0097 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 8388608 (by decide)))

def checkedGate0098 : Gate := ⟨⟨0, 0, 0⟩, ⟨16777216, 0, 16777216⟩, ⟨16777216, 0, 16777216⟩⟩
theorem checkedGate0098_join : GateValid checkedGate0098 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0099 : Gate := ⟨⟨16777216, 0, 16777216⟩, ⟨16777216, 0, 16777216⟩, ⟨33554432, 0, 33554432⟩⟩
theorem checkedGate0099_join : GateValid checkedGate0099 := by
  exact Exists.intro 0 (Exists.intro 16777216 (Exists.intro 0 (by decide)))

def checkedGate0100 : Gate := ⟨⟨0, 0, 0⟩, ⟨16777216, 16777216, 0⟩, ⟨16777216, 16777216, 0⟩⟩
theorem checkedGate0100_join : GateValid checkedGate0100 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 16777216 (by decide)))

def checkedGate0101 : Gate := ⟨⟨16777216, 16777216, 0⟩, ⟨16777216, 16777216, 0⟩, ⟨33554432, 33554432, 0⟩⟩
theorem checkedGate0101_join : GateValid checkedGate0101 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 16777216 (by decide)))

def checkedGate0102 : Gate := ⟨⟨0, 0, 0⟩, ⟨33554432, 0, 33554432⟩, ⟨33554432, 0, 33554432⟩⟩
theorem checkedGate0102_join : GateValid checkedGate0102 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0103 : Gate := ⟨⟨33554432, 0, 33554432⟩, ⟨33554432, 0, 33554432⟩, ⟨67108864, 0, 67108864⟩⟩
theorem checkedGate0103_join : GateValid checkedGate0103 := by
  exact Exists.intro 0 (Exists.intro 33554432 (Exists.intro 0 (by decide)))

def checkedGate0104 : Gate := ⟨⟨0, 0, 0⟩, ⟨33554432, 33554432, 0⟩, ⟨33554432, 33554432, 0⟩⟩
theorem checkedGate0104_join : GateValid checkedGate0104 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 33554432 (by decide)))

def checkedGate0105 : Gate := ⟨⟨33554432, 33554432, 0⟩, ⟨33554432, 33554432, 0⟩, ⟨67108864, 67108864, 0⟩⟩
theorem checkedGate0105_join : GateValid checkedGate0105 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 33554432 (by decide)))

def checkedGate0106 : Gate := ⟨⟨0, 0, 0⟩, ⟨67108864, 0, 67108864⟩, ⟨67108864, 0, 67108864⟩⟩
theorem checkedGate0106_join : GateValid checkedGate0106 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0107 : Gate := ⟨⟨67108864, 0, 67108864⟩, ⟨67108864, 0, 67108864⟩, ⟨134217728, 0, 134217728⟩⟩
theorem checkedGate0107_join : GateValid checkedGate0107 := by
  exact Exists.intro 0 (Exists.intro 67108864 (Exists.intro 0 (by decide)))

def checkedGate0108 : Gate := ⟨⟨0, 0, 0⟩, ⟨67108864, 67108864, 0⟩, ⟨67108864, 67108864, 0⟩⟩
theorem checkedGate0108_join : GateValid checkedGate0108 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 67108864 (by decide)))

def checkedGate0109 : Gate := ⟨⟨67108864, 67108864, 0⟩, ⟨67108864, 67108864, 0⟩, ⟨134217728, 134217728, 0⟩⟩
theorem checkedGate0109_join : GateValid checkedGate0109 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 67108864 (by decide)))

def checkedGate0110 : Gate := ⟨⟨0, 0, 0⟩, ⟨134217728, 0, 134217728⟩, ⟨134217728, 0, 134217728⟩⟩
theorem checkedGate0110_join : GateValid checkedGate0110 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0111 : Gate := ⟨⟨134217728, 0, 134217728⟩, ⟨134217728, 0, 134217728⟩, ⟨268435456, 0, 268435456⟩⟩
theorem checkedGate0111_join : GateValid checkedGate0111 := by
  exact Exists.intro 0 (Exists.intro 134217728 (Exists.intro 0 (by decide)))

def checkedGate0112 : Gate := ⟨⟨0, 0, 0⟩, ⟨134217728, 134217728, 0⟩, ⟨134217728, 134217728, 0⟩⟩
theorem checkedGate0112_join : GateValid checkedGate0112 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 134217728 (by decide)))

def checkedGate0113 : Gate := ⟨⟨134217728, 134217728, 0⟩, ⟨134217728, 134217728, 0⟩, ⟨268435456, 268435456, 0⟩⟩
theorem checkedGate0113_join : GateValid checkedGate0113 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 134217728 (by decide)))

def checkedGate0114 : Gate := ⟨⟨0, 0, 0⟩, ⟨268435456, 0, 268435456⟩, ⟨268435456, 0, 268435456⟩⟩
theorem checkedGate0114_join : GateValid checkedGate0114 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0115 : Gate := ⟨⟨268435456, 0, 268435456⟩, ⟨268435456, 0, 268435456⟩, ⟨536870912, 0, 536870912⟩⟩
theorem checkedGate0115_join : GateValid checkedGate0115 := by
  exact Exists.intro 0 (Exists.intro 268435456 (Exists.intro 0 (by decide)))

def checkedGate0116 : Gate := ⟨⟨0, 0, 0⟩, ⟨268435456, 268435456, 0⟩, ⟨268435456, 268435456, 0⟩⟩
theorem checkedGate0116_join : GateValid checkedGate0116 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 268435456 (by decide)))

def checkedGate0117 : Gate := ⟨⟨268435456, 268435456, 0⟩, ⟨268435456, 268435456, 0⟩, ⟨536870912, 536870912, 0⟩⟩
theorem checkedGate0117_join : GateValid checkedGate0117 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 268435456 (by decide)))

def checkedGate0118 : Gate := ⟨⟨0, 0, 0⟩, ⟨536870912, 0, 536870912⟩, ⟨536870912, 0, 536870912⟩⟩
theorem checkedGate0118_join : GateValid checkedGate0118 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0119 : Gate := ⟨⟨536870912, 0, 536870912⟩, ⟨536870912, 0, 536870912⟩, ⟨1073741824, 0, 1073741824⟩⟩
theorem checkedGate0119_join : GateValid checkedGate0119 := by
  exact Exists.intro 0 (Exists.intro 536870912 (Exists.intro 0 (by decide)))

def checkedGate0120 : Gate := ⟨⟨0, 0, 0⟩, ⟨536870912, 536870912, 0⟩, ⟨536870912, 536870912, 0⟩⟩
theorem checkedGate0120_join : GateValid checkedGate0120 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 536870912 (by decide)))

def checkedGate0121 : Gate := ⟨⟨536870912, 536870912, 0⟩, ⟨536870912, 536870912, 0⟩, ⟨1073741824, 1073741824, 0⟩⟩
theorem checkedGate0121_join : GateValid checkedGate0121 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 536870912 (by decide)))

def checkedGate0122 : Gate := ⟨⟨0, 0, 0⟩, ⟨1073741824, 0, 1073741824⟩, ⟨1073741824, 0, 1073741824⟩⟩
theorem checkedGate0122_join : GateValid checkedGate0122 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0123 : Gate := ⟨⟨1073741824, 0, 1073741824⟩, ⟨1073741824, 0, 1073741824⟩, ⟨2147483648, 0, 2147483648⟩⟩
theorem checkedGate0123_join : GateValid checkedGate0123 := by
  exact Exists.intro 0 (Exists.intro 1073741824 (Exists.intro 0 (by decide)))

def checkedGate0124 : Gate := ⟨⟨0, 0, 0⟩, ⟨1073741824, 1073741824, 0⟩, ⟨1073741824, 1073741824, 0⟩⟩
theorem checkedGate0124_join : GateValid checkedGate0124 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1073741824 (by decide)))

def checkedGate0125 : Gate := ⟨⟨1073741824, 1073741824, 0⟩, ⟨1073741824, 1073741824, 0⟩, ⟨2147483648, 2147483648, 0⟩⟩
theorem checkedGate0125_join : GateValid checkedGate0125 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1073741824 (by decide)))

def checkedGate0126 : Gate := ⟨⟨0, 0, 0⟩, ⟨2147483648, 0, 2147483648⟩, ⟨2147483648, 0, 2147483648⟩⟩
theorem checkedGate0126_join : GateValid checkedGate0126 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0127 : Gate := ⟨⟨2147483648, 0, 2147483648⟩, ⟨2147483648, 0, 2147483648⟩, ⟨4294967296, 0, 4294967296⟩⟩
theorem checkedGate0127_join : GateValid checkedGate0127 := by
  exact Exists.intro 0 (Exists.intro 2147483648 (Exists.intro 0 (by decide)))

def checkedGate0128 : Gate := ⟨⟨0, 0, 0⟩, ⟨2147483648, 2147483648, 0⟩, ⟨2147483648, 2147483648, 0⟩⟩
theorem checkedGate0128_join : GateValid checkedGate0128 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2147483648 (by decide)))

def checkedGate0129 : Gate := ⟨⟨2147483648, 2147483648, 0⟩, ⟨2147483648, 2147483648, 0⟩, ⟨4294967296, 4294967296, 0⟩⟩
theorem checkedGate0129_join : GateValid checkedGate0129 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2147483648 (by decide)))

def checkedGate0130 : Gate := ⟨⟨0, 0, 0⟩, ⟨4294967296, 0, 4294967296⟩, ⟨4294967296, 0, 4294967296⟩⟩
theorem checkedGate0130_join : GateValid checkedGate0130 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0131 : Gate := ⟨⟨4294967296, 0, 4294967296⟩, ⟨4294967296, 0, 4294967296⟩, ⟨8589934592, 0, 8589934592⟩⟩
theorem checkedGate0131_join : GateValid checkedGate0131 := by
  exact Exists.intro 0 (Exists.intro 4294967296 (Exists.intro 0 (by decide)))

def checkedGate0132 : Gate := ⟨⟨0, 0, 0⟩, ⟨4294967296, 4294967296, 0⟩, ⟨4294967296, 4294967296, 0⟩⟩
theorem checkedGate0132_join : GateValid checkedGate0132 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4294967296 (by decide)))

def checkedGate0133 : Gate := ⟨⟨4294967296, 4294967296, 0⟩, ⟨4294967296, 4294967296, 0⟩, ⟨8589934592, 8589934592, 0⟩⟩
theorem checkedGate0133_join : GateValid checkedGate0133 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4294967296 (by decide)))

def checkedGate0134 : Gate := ⟨⟨0, 0, 0⟩, ⟨8589934592, 0, 8589934592⟩, ⟨8589934592, 0, 8589934592⟩⟩
theorem checkedGate0134_join : GateValid checkedGate0134 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0135 : Gate := ⟨⟨8589934592, 0, 8589934592⟩, ⟨8589934592, 0, 8589934592⟩, ⟨17179869184, 0, 17179869184⟩⟩
theorem checkedGate0135_join : GateValid checkedGate0135 := by
  exact Exists.intro 0 (Exists.intro 8589934592 (Exists.intro 0 (by decide)))

def checkedGate0136 : Gate := ⟨⟨0, 0, 0⟩, ⟨8589934592, 8589934592, 0⟩, ⟨8589934592, 8589934592, 0⟩⟩
theorem checkedGate0136_join : GateValid checkedGate0136 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 8589934592 (by decide)))

def checkedGate0137 : Gate := ⟨⟨8589934592, 8589934592, 0⟩, ⟨8589934592, 8589934592, 0⟩, ⟨17179869184, 17179869184, 0⟩⟩
theorem checkedGate0137_join : GateValid checkedGate0137 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 8589934592 (by decide)))

def checkedGate0138 : Gate := ⟨⟨0, 0, 0⟩, ⟨17179869184, 0, 17179869184⟩, ⟨17179869184, 0, 17179869184⟩⟩
theorem checkedGate0138_join : GateValid checkedGate0138 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0139 : Gate := ⟨⟨17179869184, 0, 17179869184⟩, ⟨17179869184, 0, 17179869184⟩, ⟨34359738368, 0, 34359738368⟩⟩
theorem checkedGate0139_join : GateValid checkedGate0139 := by
  exact Exists.intro 0 (Exists.intro 17179869184 (Exists.intro 0 (by decide)))

def checkedGate0140 : Gate := ⟨⟨0, 0, 0⟩, ⟨17179869184, 17179869184, 0⟩, ⟨17179869184, 17179869184, 0⟩⟩
theorem checkedGate0140_join : GateValid checkedGate0140 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 17179869184 (by decide)))

def checkedGate0141 : Gate := ⟨⟨17179869184, 17179869184, 0⟩, ⟨17179869184, 17179869184, 0⟩, ⟨34359738368, 34359738368, 0⟩⟩
theorem checkedGate0141_join : GateValid checkedGate0141 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 17179869184 (by decide)))

def checkedGate0142 : Gate := ⟨⟨0, 0, 0⟩, ⟨34359738368, 0, 34359738368⟩, ⟨34359738368, 0, 34359738368⟩⟩
theorem checkedGate0142_join : GateValid checkedGate0142 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0143 : Gate := ⟨⟨34359738368, 0, 34359738368⟩, ⟨34359738368, 0, 34359738368⟩, ⟨68719476736, 0, 68719476736⟩⟩
theorem checkedGate0143_join : GateValid checkedGate0143 := by
  exact Exists.intro 0 (Exists.intro 34359738368 (Exists.intro 0 (by decide)))

def checkedGate0144 : Gate := ⟨⟨0, 0, 0⟩, ⟨34359738368, 34359738368, 0⟩, ⟨34359738368, 34359738368, 0⟩⟩
theorem checkedGate0144_join : GateValid checkedGate0144 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 34359738368 (by decide)))

def checkedGate0145 : Gate := ⟨⟨34359738368, 34359738368, 0⟩, ⟨34359738368, 34359738368, 0⟩, ⟨68719476736, 68719476736, 0⟩⟩
theorem checkedGate0145_join : GateValid checkedGate0145 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 34359738368 (by decide)))

def checkedGate0146 : Gate := ⟨⟨0, 0, 0⟩, ⟨68719476736, 0, 68719476736⟩, ⟨68719476736, 0, 68719476736⟩⟩
theorem checkedGate0146_join : GateValid checkedGate0146 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0147 : Gate := ⟨⟨68719476736, 0, 68719476736⟩, ⟨68719476736, 0, 68719476736⟩, ⟨137438953472, 0, 137438953472⟩⟩
theorem checkedGate0147_join : GateValid checkedGate0147 := by
  exact Exists.intro 0 (Exists.intro 68719476736 (Exists.intro 0 (by decide)))

def checkedGate0148 : Gate := ⟨⟨0, 0, 0⟩, ⟨68719476736, 68719476736, 0⟩, ⟨68719476736, 68719476736, 0⟩⟩
theorem checkedGate0148_join : GateValid checkedGate0148 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 68719476736 (by decide)))

def checkedGate0149 : Gate := ⟨⟨68719476736, 68719476736, 0⟩, ⟨68719476736, 68719476736, 0⟩, ⟨137438953472, 137438953472, 0⟩⟩
theorem checkedGate0149_join : GateValid checkedGate0149 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 68719476736 (by decide)))

def checkedGate0150 : Gate := ⟨⟨0, 0, 0⟩, ⟨137438953472, 0, 137438953472⟩, ⟨137438953472, 0, 137438953472⟩⟩
theorem checkedGate0150_join : GateValid checkedGate0150 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0151 : Gate := ⟨⟨137438953472, 0, 137438953472⟩, ⟨137438953472, 0, 137438953472⟩, ⟨274877906944, 0, 274877906944⟩⟩
theorem checkedGate0151_join : GateValid checkedGate0151 := by
  exact Exists.intro 0 (Exists.intro 137438953472 (Exists.intro 0 (by decide)))

def checkedGate0152 : Gate := ⟨⟨0, 0, 0⟩, ⟨137438953472, 137438953472, 0⟩, ⟨137438953472, 137438953472, 0⟩⟩
theorem checkedGate0152_join : GateValid checkedGate0152 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 137438953472 (by decide)))

def checkedGate0153 : Gate := ⟨⟨137438953472, 137438953472, 0⟩, ⟨137438953472, 137438953472, 0⟩, ⟨274877906944, 274877906944, 0⟩⟩
theorem checkedGate0153_join : GateValid checkedGate0153 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 137438953472 (by decide)))

def checkedGate0154 : Gate := ⟨⟨0, 0, 0⟩, ⟨274877906944, 0, 274877906944⟩, ⟨274877906944, 0, 274877906944⟩⟩
theorem checkedGate0154_join : GateValid checkedGate0154 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0155 : Gate := ⟨⟨274877906944, 0, 274877906944⟩, ⟨274877906944, 0, 274877906944⟩, ⟨549755813888, 0, 549755813888⟩⟩
theorem checkedGate0155_join : GateValid checkedGate0155 := by
  exact Exists.intro 0 (Exists.intro 274877906944 (Exists.intro 0 (by decide)))

def checkedGate0156 : Gate := ⟨⟨0, 0, 0⟩, ⟨274877906944, 274877906944, 0⟩, ⟨274877906944, 274877906944, 0⟩⟩
theorem checkedGate0156_join : GateValid checkedGate0156 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 274877906944 (by decide)))

def checkedGate0157 : Gate := ⟨⟨274877906944, 274877906944, 0⟩, ⟨274877906944, 274877906944, 0⟩, ⟨549755813888, 549755813888, 0⟩⟩
theorem checkedGate0157_join : GateValid checkedGate0157 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 274877906944 (by decide)))

def checkedGate0158 : Gate := ⟨⟨0, 0, 0⟩, ⟨549755813888, 0, 549755813888⟩, ⟨549755813888, 0, 549755813888⟩⟩
theorem checkedGate0158_join : GateValid checkedGate0158 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0159 : Gate := ⟨⟨549755813888, 0, 549755813888⟩, ⟨549755813888, 0, 549755813888⟩, ⟨1099511627776, 0, 1099511627776⟩⟩
theorem checkedGate0159_join : GateValid checkedGate0159 := by
  exact Exists.intro 0 (Exists.intro 549755813888 (Exists.intro 0 (by decide)))

def checkedGate0160 : Gate := ⟨⟨0, 0, 0⟩, ⟨549755813888, 549755813888, 0⟩, ⟨549755813888, 549755813888, 0⟩⟩
theorem checkedGate0160_join : GateValid checkedGate0160 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 549755813888 (by decide)))

def checkedGate0161 : Gate := ⟨⟨549755813888, 549755813888, 0⟩, ⟨549755813888, 549755813888, 0⟩, ⟨1099511627776, 1099511627776, 0⟩⟩
theorem checkedGate0161_join : GateValid checkedGate0161 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 549755813888 (by decide)))

def checkedGate0162 : Gate := ⟨⟨0, 0, 0⟩, ⟨1099511627776, 0, 1099511627776⟩, ⟨1099511627776, 0, 1099511627776⟩⟩
theorem checkedGate0162_join : GateValid checkedGate0162 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0163 : Gate := ⟨⟨1099511627776, 0, 1099511627776⟩, ⟨1099511627776, 0, 1099511627776⟩, ⟨2199023255552, 0, 2199023255552⟩⟩
theorem checkedGate0163_join : GateValid checkedGate0163 := by
  exact Exists.intro 0 (Exists.intro 1099511627776 (Exists.intro 0 (by decide)))

def checkedGate0164 : Gate := ⟨⟨0, 0, 0⟩, ⟨1099511627776, 1099511627776, 0⟩, ⟨1099511627776, 1099511627776, 0⟩⟩
theorem checkedGate0164_join : GateValid checkedGate0164 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1099511627776 (by decide)))

def checkedGate0165 : Gate := ⟨⟨1099511627776, 1099511627776, 0⟩, ⟨1099511627776, 1099511627776, 0⟩, ⟨2199023255552, 2199023255552, 0⟩⟩
theorem checkedGate0165_join : GateValid checkedGate0165 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1099511627776 (by decide)))

def checkedGate0166 : Gate := ⟨⟨0, 0, 0⟩, ⟨2199023255552, 0, 2199023255552⟩, ⟨2199023255552, 0, 2199023255552⟩⟩
theorem checkedGate0166_join : GateValid checkedGate0166 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0167 : Gate := ⟨⟨2199023255552, 0, 2199023255552⟩, ⟨2199023255552, 0, 2199023255552⟩, ⟨4398046511104, 0, 4398046511104⟩⟩
theorem checkedGate0167_join : GateValid checkedGate0167 := by
  exact Exists.intro 0 (Exists.intro 2199023255552 (Exists.intro 0 (by decide)))

def checkedGate0168 : Gate := ⟨⟨0, 0, 0⟩, ⟨2199023255552, 2199023255552, 0⟩, ⟨2199023255552, 2199023255552, 0⟩⟩
theorem checkedGate0168_join : GateValid checkedGate0168 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2199023255552 (by decide)))

def checkedGate0169 : Gate := ⟨⟨2199023255552, 2199023255552, 0⟩, ⟨2199023255552, 2199023255552, 0⟩, ⟨4398046511104, 4398046511104, 0⟩⟩
theorem checkedGate0169_join : GateValid checkedGate0169 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2199023255552 (by decide)))

def checkedGate0170 : Gate := ⟨⟨0, 0, 0⟩, ⟨4398046511104, 0, 4398046511104⟩, ⟨4398046511104, 0, 4398046511104⟩⟩
theorem checkedGate0170_join : GateValid checkedGate0170 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0171 : Gate := ⟨⟨4398046511104, 0, 4398046511104⟩, ⟨4398046511104, 0, 4398046511104⟩, ⟨8796093022208, 0, 8796093022208⟩⟩
theorem checkedGate0171_join : GateValid checkedGate0171 := by
  exact Exists.intro 0 (Exists.intro 4398046511104 (Exists.intro 0 (by decide)))

def checkedGate0172 : Gate := ⟨⟨0, 0, 0⟩, ⟨4398046511104, 4398046511104, 0⟩, ⟨4398046511104, 4398046511104, 0⟩⟩
theorem checkedGate0172_join : GateValid checkedGate0172 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4398046511104 (by decide)))

def checkedGate0173 : Gate := ⟨⟨4398046511104, 4398046511104, 0⟩, ⟨4398046511104, 4398046511104, 0⟩, ⟨8796093022208, 8796093022208, 0⟩⟩
theorem checkedGate0173_join : GateValid checkedGate0173 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4398046511104 (by decide)))

def checkedGate0174 : Gate := ⟨⟨0, 0, 0⟩, ⟨8796093022208, 0, 8796093022208⟩, ⟨8796093022208, 0, 8796093022208⟩⟩
theorem checkedGate0174_join : GateValid checkedGate0174 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0175 : Gate := ⟨⟨8796093022208, 0, 8796093022208⟩, ⟨8796093022208, 0, 8796093022208⟩, ⟨17592186044416, 0, 17592186044416⟩⟩
theorem checkedGate0175_join : GateValid checkedGate0175 := by
  exact Exists.intro 0 (Exists.intro 8796093022208 (Exists.intro 0 (by decide)))

def checkedGate0176 : Gate := ⟨⟨0, 0, 0⟩, ⟨8796093022208, 8796093022208, 0⟩, ⟨8796093022208, 8796093022208, 0⟩⟩
theorem checkedGate0176_join : GateValid checkedGate0176 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 8796093022208 (by decide)))

def checkedGate0177 : Gate := ⟨⟨8796093022208, 8796093022208, 0⟩, ⟨8796093022208, 8796093022208, 0⟩, ⟨17592186044416, 17592186044416, 0⟩⟩
theorem checkedGate0177_join : GateValid checkedGate0177 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 8796093022208 (by decide)))

def checkedGate0178 : Gate := ⟨⟨0, 0, 0⟩, ⟨17592186044416, 0, 17592186044416⟩, ⟨17592186044416, 0, 17592186044416⟩⟩
theorem checkedGate0178_join : GateValid checkedGate0178 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0179 : Gate := ⟨⟨17592186044416, 0, 17592186044416⟩, ⟨17592186044416, 0, 17592186044416⟩, ⟨35184372088832, 0, 35184372088832⟩⟩
theorem checkedGate0179_join : GateValid checkedGate0179 := by
  exact Exists.intro 0 (Exists.intro 17592186044416 (Exists.intro 0 (by decide)))

def checkedGate0180 : Gate := ⟨⟨0, 0, 0⟩, ⟨17592186044416, 17592186044416, 0⟩, ⟨17592186044416, 17592186044416, 0⟩⟩
theorem checkedGate0180_join : GateValid checkedGate0180 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 17592186044416 (by decide)))

def checkedGate0181 : Gate := ⟨⟨17592186044416, 17592186044416, 0⟩, ⟨17592186044416, 17592186044416, 0⟩, ⟨35184372088832, 35184372088832, 0⟩⟩
theorem checkedGate0181_join : GateValid checkedGate0181 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 17592186044416 (by decide)))

def checkedGate0182 : Gate := ⟨⟨0, 0, 0⟩, ⟨35184372088832, 0, 35184372088832⟩, ⟨35184372088832, 0, 35184372088832⟩⟩
theorem checkedGate0182_join : GateValid checkedGate0182 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0183 : Gate := ⟨⟨35184372088832, 0, 35184372088832⟩, ⟨35184372088832, 0, 35184372088832⟩, ⟨70368744177664, 0, 70368744177664⟩⟩
theorem checkedGate0183_join : GateValid checkedGate0183 := by
  exact Exists.intro 0 (Exists.intro 35184372088832 (Exists.intro 0 (by decide)))

def checkedGate0184 : Gate := ⟨⟨0, 0, 0⟩, ⟨35184372088832, 35184372088832, 0⟩, ⟨35184372088832, 35184372088832, 0⟩⟩
theorem checkedGate0184_join : GateValid checkedGate0184 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 35184372088832 (by decide)))

def checkedGate0185 : Gate := ⟨⟨35184372088832, 35184372088832, 0⟩, ⟨35184372088832, 35184372088832, 0⟩, ⟨70368744177664, 70368744177664, 0⟩⟩
theorem checkedGate0185_join : GateValid checkedGate0185 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 35184372088832 (by decide)))

def checkedGate0186 : Gate := ⟨⟨0, 0, 0⟩, ⟨70368744177664, 0, 70368744177664⟩, ⟨70368744177664, 0, 70368744177664⟩⟩
theorem checkedGate0186_join : GateValid checkedGate0186 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0187 : Gate := ⟨⟨70368744177664, 0, 70368744177664⟩, ⟨70368744177664, 0, 70368744177664⟩, ⟨140737488355328, 0, 140737488355328⟩⟩
theorem checkedGate0187_join : GateValid checkedGate0187 := by
  exact Exists.intro 0 (Exists.intro 70368744177664 (Exists.intro 0 (by decide)))

def checkedGate0188 : Gate := ⟨⟨0, 0, 0⟩, ⟨70368744177664, 70368744177664, 0⟩, ⟨70368744177664, 70368744177664, 0⟩⟩
theorem checkedGate0188_join : GateValid checkedGate0188 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 70368744177664 (by decide)))

def checkedGate0189 : Gate := ⟨⟨70368744177664, 70368744177664, 0⟩, ⟨70368744177664, 70368744177664, 0⟩, ⟨140737488355328, 140737488355328, 0⟩⟩
theorem checkedGate0189_join : GateValid checkedGate0189 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 70368744177664 (by decide)))

def checkedGate0190 : Gate := ⟨⟨0, 0, 0⟩, ⟨140737488355328, 0, 140737488355328⟩, ⟨140737488355328, 0, 140737488355328⟩⟩
theorem checkedGate0190_join : GateValid checkedGate0190 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0191 : Gate := ⟨⟨140737488355328, 0, 140737488355328⟩, ⟨140737488355328, 0, 140737488355328⟩, ⟨281474976710656, 0, 281474976710656⟩⟩
theorem checkedGate0191_join : GateValid checkedGate0191 := by
  exact Exists.intro 0 (Exists.intro 140737488355328 (Exists.intro 0 (by decide)))

def checkedGate0192 : Gate := ⟨⟨0, 0, 0⟩, ⟨140737488355328, 140737488355328, 0⟩, ⟨140737488355328, 140737488355328, 0⟩⟩
theorem checkedGate0192_join : GateValid checkedGate0192 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 140737488355328 (by decide)))

def checkedGate0193 : Gate := ⟨⟨140737488355328, 140737488355328, 0⟩, ⟨140737488355328, 140737488355328, 0⟩, ⟨281474976710656, 281474976710656, 0⟩⟩
theorem checkedGate0193_join : GateValid checkedGate0193 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 140737488355328 (by decide)))

def checkedGate0194 : Gate := ⟨⟨0, 0, 0⟩, ⟨281474976710656, 0, 281474976710656⟩, ⟨281474976710656, 0, 281474976710656⟩⟩
theorem checkedGate0194_join : GateValid checkedGate0194 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0195 : Gate := ⟨⟨281474976710656, 0, 281474976710656⟩, ⟨281474976710656, 0, 281474976710656⟩, ⟨562949953421312, 0, 562949953421312⟩⟩
theorem checkedGate0195_join : GateValid checkedGate0195 := by
  exact Exists.intro 0 (Exists.intro 281474976710656 (Exists.intro 0 (by decide)))

def checkedGate0196 : Gate := ⟨⟨0, 0, 0⟩, ⟨281474976710656, 281474976710656, 0⟩, ⟨281474976710656, 281474976710656, 0⟩⟩
theorem checkedGate0196_join : GateValid checkedGate0196 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 281474976710656 (by decide)))

def checkedGate0197 : Gate := ⟨⟨281474976710656, 281474976710656, 0⟩, ⟨281474976710656, 281474976710656, 0⟩, ⟨562949953421312, 562949953421312, 0⟩⟩
theorem checkedGate0197_join : GateValid checkedGate0197 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 281474976710656 (by decide)))

def checkedGate0198 : Gate := ⟨⟨0, 0, 0⟩, ⟨562949953421312, 0, 562949953421312⟩, ⟨562949953421312, 0, 562949953421312⟩⟩
theorem checkedGate0198_join : GateValid checkedGate0198 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0199 : Gate := ⟨⟨562949953421312, 0, 562949953421312⟩, ⟨562949953421312, 0, 562949953421312⟩, ⟨1125899906842624, 0, 1125899906842624⟩⟩
theorem checkedGate0199_join : GateValid checkedGate0199 := by
  exact Exists.intro 0 (Exists.intro 562949953421312 (Exists.intro 0 (by decide)))

def checkedGate0200 : Gate := ⟨⟨0, 0, 0⟩, ⟨562949953421312, 562949953421312, 0⟩, ⟨562949953421312, 562949953421312, 0⟩⟩
theorem checkedGate0200_join : GateValid checkedGate0200 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 562949953421312 (by decide)))

def checkedGate0201 : Gate := ⟨⟨562949953421312, 562949953421312, 0⟩, ⟨562949953421312, 562949953421312, 0⟩, ⟨1125899906842624, 1125899906842624, 0⟩⟩
theorem checkedGate0201_join : GateValid checkedGate0201 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 562949953421312 (by decide)))

def checkedGate0202 : Gate := ⟨⟨0, 0, 0⟩, ⟨1125899906842624, 0, 1125899906842624⟩, ⟨1125899906842624, 0, 1125899906842624⟩⟩
theorem checkedGate0202_join : GateValid checkedGate0202 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0203 : Gate := ⟨⟨1125899906842624, 0, 1125899906842624⟩, ⟨1125899906842624, 0, 1125899906842624⟩, ⟨2251799813685248, 0, 2251799813685248⟩⟩
theorem checkedGate0203_join : GateValid checkedGate0203 := by
  exact Exists.intro 0 (Exists.intro 1125899906842624 (Exists.intro 0 (by decide)))

def checkedGate0204 : Gate := ⟨⟨0, 0, 0⟩, ⟨1125899906842624, 1125899906842624, 0⟩, ⟨1125899906842624, 1125899906842624, 0⟩⟩
theorem checkedGate0204_join : GateValid checkedGate0204 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1125899906842624 (by decide)))

def checkedGate0205 : Gate := ⟨⟨1125899906842624, 1125899906842624, 0⟩, ⟨1125899906842624, 1125899906842624, 0⟩, ⟨2251799813685248, 2251799813685248, 0⟩⟩
theorem checkedGate0205_join : GateValid checkedGate0205 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1125899906842624 (by decide)))

def checkedGate0206 : Gate := ⟨⟨0, 0, 0⟩, ⟨2251799813685248, 0, 2251799813685248⟩, ⟨2251799813685248, 0, 2251799813685248⟩⟩
theorem checkedGate0206_join : GateValid checkedGate0206 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0207 : Gate := ⟨⟨2251799813685248, 0, 2251799813685248⟩, ⟨2251799813685248, 0, 2251799813685248⟩, ⟨4503599627370496, 0, 4503599627370496⟩⟩
theorem checkedGate0207_join : GateValid checkedGate0207 := by
  exact Exists.intro 0 (Exists.intro 2251799813685248 (Exists.intro 0 (by decide)))

def checkedGate0208 : Gate := ⟨⟨0, 0, 0⟩, ⟨2251799813685248, 2251799813685248, 0⟩, ⟨2251799813685248, 2251799813685248, 0⟩⟩
theorem checkedGate0208_join : GateValid checkedGate0208 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2251799813685248 (by decide)))

def checkedGate0209 : Gate := ⟨⟨2251799813685248, 2251799813685248, 0⟩, ⟨2251799813685248, 2251799813685248, 0⟩, ⟨4503599627370496, 4503599627370496, 0⟩⟩
theorem checkedGate0209_join : GateValid checkedGate0209 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2251799813685248 (by decide)))

def checkedGate0210 : Gate := ⟨⟨0, 0, 0⟩, ⟨4503599627370496, 0, 4503599627370496⟩, ⟨4503599627370496, 0, 4503599627370496⟩⟩
theorem checkedGate0210_join : GateValid checkedGate0210 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0211 : Gate := ⟨⟨4503599627370496, 0, 4503599627370496⟩, ⟨4503599627370496, 0, 4503599627370496⟩, ⟨9007199254740992, 0, 9007199254740992⟩⟩
theorem checkedGate0211_join : GateValid checkedGate0211 := by
  exact Exists.intro 0 (Exists.intro 4503599627370496 (Exists.intro 0 (by decide)))

def checkedGate0212 : Gate := ⟨⟨0, 0, 0⟩, ⟨4503599627370496, 4503599627370496, 0⟩, ⟨4503599627370496, 4503599627370496, 0⟩⟩
theorem checkedGate0212_join : GateValid checkedGate0212 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4503599627370496 (by decide)))

def checkedGate0213 : Gate := ⟨⟨4503599627370496, 4503599627370496, 0⟩, ⟨4503599627370496, 4503599627370496, 0⟩, ⟨9007199254740992, 9007199254740992, 0⟩⟩
theorem checkedGate0213_join : GateValid checkedGate0213 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4503599627370496 (by decide)))

def checkedGate0214 : Gate := ⟨⟨0, 0, 0⟩, ⟨9007199254740992, 0, 9007199254740992⟩, ⟨9007199254740992, 0, 9007199254740992⟩⟩
theorem checkedGate0214_join : GateValid checkedGate0214 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0215 : Gate := ⟨⟨9007199254740992, 0, 9007199254740992⟩, ⟨9007199254740992, 0, 9007199254740992⟩, ⟨18014398509481984, 0, 18014398509481984⟩⟩
theorem checkedGate0215_join : GateValid checkedGate0215 := by
  exact Exists.intro 0 (Exists.intro 9007199254740992 (Exists.intro 0 (by decide)))

def checkedGate0216 : Gate := ⟨⟨0, 0, 0⟩, ⟨9007199254740992, 9007199254740992, 0⟩, ⟨9007199254740992, 9007199254740992, 0⟩⟩
theorem checkedGate0216_join : GateValid checkedGate0216 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 9007199254740992 (by decide)))

def checkedGate0217 : Gate := ⟨⟨9007199254740992, 9007199254740992, 0⟩, ⟨9007199254740992, 9007199254740992, 0⟩, ⟨18014398509481984, 18014398509481984, 0⟩⟩
theorem checkedGate0217_join : GateValid checkedGate0217 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 9007199254740992 (by decide)))

def checkedGate0218 : Gate := ⟨⟨0, 0, 0⟩, ⟨18014398509481984, 0, 18014398509481984⟩, ⟨18014398509481984, 0, 18014398509481984⟩⟩
theorem checkedGate0218_join : GateValid checkedGate0218 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0219 : Gate := ⟨⟨18014398509481984, 0, 18014398509481984⟩, ⟨18014398509481984, 0, 18014398509481984⟩, ⟨36028797018963968, 0, 36028797018963968⟩⟩
theorem checkedGate0219_join : GateValid checkedGate0219 := by
  exact Exists.intro 0 (Exists.intro 18014398509481984 (Exists.intro 0 (by decide)))

def checkedGate0220 : Gate := ⟨⟨0, 0, 0⟩, ⟨18014398509481984, 18014398509481984, 0⟩, ⟨18014398509481984, 18014398509481984, 0⟩⟩
theorem checkedGate0220_join : GateValid checkedGate0220 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 18014398509481984 (by decide)))

def checkedGate0221 : Gate := ⟨⟨18014398509481984, 18014398509481984, 0⟩, ⟨18014398509481984, 18014398509481984, 0⟩, ⟨36028797018963968, 36028797018963968, 0⟩⟩
theorem checkedGate0221_join : GateValid checkedGate0221 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 18014398509481984 (by decide)))

def checkedGate0222 : Gate := ⟨⟨0, 0, 0⟩, ⟨36028797018963968, 0, 36028797018963968⟩, ⟨36028797018963968, 0, 36028797018963968⟩⟩
theorem checkedGate0222_join : GateValid checkedGate0222 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0223 : Gate := ⟨⟨36028797018963968, 0, 36028797018963968⟩, ⟨36028797018963968, 0, 36028797018963968⟩, ⟨72057594037927936, 0, 72057594037927936⟩⟩
theorem checkedGate0223_join : GateValid checkedGate0223 := by
  exact Exists.intro 0 (Exists.intro 36028797018963968 (Exists.intro 0 (by decide)))

def checkedGate0224 : Gate := ⟨⟨0, 0, 0⟩, ⟨36028797018963968, 36028797018963968, 0⟩, ⟨36028797018963968, 36028797018963968, 0⟩⟩
theorem checkedGate0224_join : GateValid checkedGate0224 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 36028797018963968 (by decide)))

def checkedGate0225 : Gate := ⟨⟨36028797018963968, 36028797018963968, 0⟩, ⟨36028797018963968, 36028797018963968, 0⟩, ⟨72057594037927936, 72057594037927936, 0⟩⟩
theorem checkedGate0225_join : GateValid checkedGate0225 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 36028797018963968 (by decide)))

def checkedGate0226 : Gate := ⟨⟨0, 0, 0⟩, ⟨72057594037927936, 0, 72057594037927936⟩, ⟨72057594037927936, 0, 72057594037927936⟩⟩
theorem checkedGate0226_join : GateValid checkedGate0226 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0227 : Gate := ⟨⟨72057594037927936, 0, 72057594037927936⟩, ⟨72057594037927936, 0, 72057594037927936⟩, ⟨144115188075855872, 0, 144115188075855872⟩⟩
theorem checkedGate0227_join : GateValid checkedGate0227 := by
  exact Exists.intro 0 (Exists.intro 72057594037927936 (Exists.intro 0 (by decide)))

def checkedGate0228 : Gate := ⟨⟨0, 0, 0⟩, ⟨72057594037927936, 72057594037927936, 0⟩, ⟨72057594037927936, 72057594037927936, 0⟩⟩
theorem checkedGate0228_join : GateValid checkedGate0228 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 72057594037927936 (by decide)))

def checkedGate0229 : Gate := ⟨⟨72057594037927936, 72057594037927936, 0⟩, ⟨72057594037927936, 72057594037927936, 0⟩, ⟨144115188075855872, 144115188075855872, 0⟩⟩
theorem checkedGate0229_join : GateValid checkedGate0229 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 72057594037927936 (by decide)))

def checkedGate0230 : Gate := ⟨⟨0, 0, 0⟩, ⟨144115188075855872, 0, 144115188075855872⟩, ⟨144115188075855872, 0, 144115188075855872⟩⟩
theorem checkedGate0230_join : GateValid checkedGate0230 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0231 : Gate := ⟨⟨144115188075855872, 0, 144115188075855872⟩, ⟨144115188075855872, 0, 144115188075855872⟩, ⟨288230376151711744, 0, 288230376151711744⟩⟩
theorem checkedGate0231_join : GateValid checkedGate0231 := by
  exact Exists.intro 0 (Exists.intro 144115188075855872 (Exists.intro 0 (by decide)))

def checkedGate0232 : Gate := ⟨⟨0, 0, 0⟩, ⟨144115188075855872, 144115188075855872, 0⟩, ⟨144115188075855872, 144115188075855872, 0⟩⟩
theorem checkedGate0232_join : GateValid checkedGate0232 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 144115188075855872 (by decide)))

def checkedGate0233 : Gate := ⟨⟨144115188075855872, 144115188075855872, 0⟩, ⟨144115188075855872, 144115188075855872, 0⟩, ⟨288230376151711744, 288230376151711744, 0⟩⟩
theorem checkedGate0233_join : GateValid checkedGate0233 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 144115188075855872 (by decide)))

def checkedGate0234 : Gate := ⟨⟨0, 0, 0⟩, ⟨288230376151711744, 0, 288230376151711744⟩, ⟨288230376151711744, 0, 288230376151711744⟩⟩
theorem checkedGate0234_join : GateValid checkedGate0234 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0235 : Gate := ⟨⟨288230376151711744, 0, 288230376151711744⟩, ⟨288230376151711744, 0, 288230376151711744⟩, ⟨576460752303423488, 0, 576460752303423488⟩⟩
theorem checkedGate0235_join : GateValid checkedGate0235 := by
  exact Exists.intro 0 (Exists.intro 288230376151711744 (Exists.intro 0 (by decide)))

def checkedGate0236 : Gate := ⟨⟨0, 0, 0⟩, ⟨288230376151711744, 288230376151711744, 0⟩, ⟨288230376151711744, 288230376151711744, 0⟩⟩
theorem checkedGate0236_join : GateValid checkedGate0236 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 288230376151711744 (by decide)))

def checkedGate0237 : Gate := ⟨⟨288230376151711744, 288230376151711744, 0⟩, ⟨288230376151711744, 288230376151711744, 0⟩, ⟨576460752303423488, 576460752303423488, 0⟩⟩
theorem checkedGate0237_join : GateValid checkedGate0237 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 288230376151711744 (by decide)))

def checkedGate0238 : Gate := ⟨⟨0, 0, 0⟩, ⟨576460752303423488, 0, 576460752303423488⟩, ⟨576460752303423488, 0, 576460752303423488⟩⟩
theorem checkedGate0238_join : GateValid checkedGate0238 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0239 : Gate := ⟨⟨576460752303423488, 0, 576460752303423488⟩, ⟨576460752303423488, 0, 576460752303423488⟩, ⟨1152921504606846976, 0, 1152921504606846976⟩⟩
theorem checkedGate0239_join : GateValid checkedGate0239 := by
  exact Exists.intro 0 (Exists.intro 576460752303423488 (Exists.intro 0 (by decide)))

def checkedGate0240 : Gate := ⟨⟨0, 0, 0⟩, ⟨576460752303423488, 576460752303423488, 0⟩, ⟨576460752303423488, 576460752303423488, 0⟩⟩
theorem checkedGate0240_join : GateValid checkedGate0240 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 576460752303423488 (by decide)))

def checkedGate0241 : Gate := ⟨⟨576460752303423488, 576460752303423488, 0⟩, ⟨576460752303423488, 576460752303423488, 0⟩, ⟨1152921504606846976, 1152921504606846976, 0⟩⟩
theorem checkedGate0241_join : GateValid checkedGate0241 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 576460752303423488 (by decide)))

def checkedGate0242 : Gate := ⟨⟨0, 0, 0⟩, ⟨1152921504606846976, 0, 1152921504606846976⟩, ⟨1152921504606846976, 0, 1152921504606846976⟩⟩
theorem checkedGate0242_join : GateValid checkedGate0242 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0243 : Gate := ⟨⟨1152921504606846976, 0, 1152921504606846976⟩, ⟨1152921504606846976, 0, 1152921504606846976⟩, ⟨2305843009213693952, 0, 2305843009213693952⟩⟩
theorem checkedGate0243_join : GateValid checkedGate0243 := by
  exact Exists.intro 0 (Exists.intro 1152921504606846976 (Exists.intro 0 (by decide)))

def checkedGate0244 : Gate := ⟨⟨0, 0, 0⟩, ⟨1152921504606846976, 1152921504606846976, 0⟩, ⟨1152921504606846976, 1152921504606846976, 0⟩⟩
theorem checkedGate0244_join : GateValid checkedGate0244 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1152921504606846976 (by decide)))

def checkedGate0245 : Gate := ⟨⟨1152921504606846976, 1152921504606846976, 0⟩, ⟨1152921504606846976, 1152921504606846976, 0⟩, ⟨2305843009213693952, 2305843009213693952, 0⟩⟩
theorem checkedGate0245_join : GateValid checkedGate0245 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1152921504606846976 (by decide)))

def checkedGate0246 : Gate := ⟨⟨0, 0, 0⟩, ⟨2305843009213693952, 0, 2305843009213693952⟩, ⟨2305843009213693952, 0, 2305843009213693952⟩⟩
theorem checkedGate0246_join : GateValid checkedGate0246 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0247 : Gate := ⟨⟨2305843009213693952, 0, 2305843009213693952⟩, ⟨2305843009213693952, 0, 2305843009213693952⟩, ⟨4611686018427387904, 0, 4611686018427387904⟩⟩
theorem checkedGate0247_join : GateValid checkedGate0247 := by
  exact Exists.intro 0 (Exists.intro 2305843009213693952 (Exists.intro 0 (by decide)))

def checkedGate0248 : Gate := ⟨⟨0, 0, 0⟩, ⟨2305843009213693952, 2305843009213693952, 0⟩, ⟨2305843009213693952, 2305843009213693952, 0⟩⟩
theorem checkedGate0248_join : GateValid checkedGate0248 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2305843009213693952 (by decide)))

def checkedGate0249 : Gate := ⟨⟨2305843009213693952, 2305843009213693952, 0⟩, ⟨2305843009213693952, 2305843009213693952, 0⟩, ⟨4611686018427387904, 4611686018427387904, 0⟩⟩
theorem checkedGate0249_join : GateValid checkedGate0249 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2305843009213693952 (by decide)))

def checkedGate0250 : Gate := ⟨⟨0, 0, 0⟩, ⟨4611686018427387904, 0, 4611686018427387904⟩, ⟨4611686018427387904, 0, 4611686018427387904⟩⟩
theorem checkedGate0250_join : GateValid checkedGate0250 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0251 : Gate := ⟨⟨4611686018427387904, 0, 4611686018427387904⟩, ⟨4611686018427387904, 0, 4611686018427387904⟩, ⟨9223372036854775808, 0, 9223372036854775808⟩⟩
theorem checkedGate0251_join : GateValid checkedGate0251 := by
  exact Exists.intro 0 (Exists.intro 4611686018427387904 (Exists.intro 0 (by decide)))

def checkedGate0252 : Gate := ⟨⟨0, 0, 0⟩, ⟨4611686018427387904, 4611686018427387904, 0⟩, ⟨4611686018427387904, 4611686018427387904, 0⟩⟩
theorem checkedGate0252_join : GateValid checkedGate0252 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4611686018427387904 (by decide)))

def checkedGate0253 : Gate := ⟨⟨4611686018427387904, 4611686018427387904, 0⟩, ⟨4611686018427387904, 4611686018427387904, 0⟩, ⟨9223372036854775808, 9223372036854775808, 0⟩⟩
theorem checkedGate0253_join : GateValid checkedGate0253 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4611686018427387904 (by decide)))

def checkedGate0254 : Gate := ⟨⟨0, 0, 0⟩, ⟨9223372036854775808, 0, 9223372036854775808⟩, ⟨9223372036854775808, 0, 9223372036854775808⟩⟩
theorem checkedGate0254_join : GateValid checkedGate0254 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0255 : Gate := ⟨⟨9223372036854775808, 0, 9223372036854775808⟩, ⟨9223372036854775808, 0, 9223372036854775808⟩, ⟨18446744073709551616, 0, 18446744073709551616⟩⟩
theorem checkedGate0255_join : GateValid checkedGate0255 := by
  exact Exists.intro 0 (Exists.intro 9223372036854775808 (Exists.intro 0 (by decide)))

def checkedGate0256 : Gate := ⟨⟨0, 0, 0⟩, ⟨9223372036854775808, 9223372036854775808, 0⟩, ⟨9223372036854775808, 9223372036854775808, 0⟩⟩
theorem checkedGate0256_join : GateValid checkedGate0256 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 9223372036854775808 (by decide)))

def checkedGate0257 : Gate := ⟨⟨9223372036854775808, 9223372036854775808, 0⟩, ⟨9223372036854775808, 9223372036854775808, 0⟩, ⟨18446744073709551616, 18446744073709551616, 0⟩⟩
theorem checkedGate0257_join : GateValid checkedGate0257 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 9223372036854775808 (by decide)))

def checkedGate0258 : Gate := ⟨⟨0, 0, 0⟩, ⟨18446744073709551616, 0, 18446744073709551616⟩, ⟨18446744073709551616, 0, 18446744073709551616⟩⟩
theorem checkedGate0258_join : GateValid checkedGate0258 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0259 : Gate := ⟨⟨18446744073709551616, 0, 18446744073709551616⟩, ⟨18446744073709551616, 0, 18446744073709551616⟩, ⟨36893488147419103232, 0, 36893488147419103232⟩⟩
theorem checkedGate0259_join : GateValid checkedGate0259 := by
  exact Exists.intro 0 (Exists.intro 18446744073709551616 (Exists.intro 0 (by decide)))

def checkedGate0260 : Gate := ⟨⟨0, 0, 0⟩, ⟨18446744073709551616, 18446744073709551616, 0⟩, ⟨18446744073709551616, 18446744073709551616, 0⟩⟩
theorem checkedGate0260_join : GateValid checkedGate0260 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 18446744073709551616 (by decide)))

def checkedGate0261 : Gate := ⟨⟨18446744073709551616, 18446744073709551616, 0⟩, ⟨18446744073709551616, 18446744073709551616, 0⟩, ⟨36893488147419103232, 36893488147419103232, 0⟩⟩
theorem checkedGate0261_join : GateValid checkedGate0261 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 18446744073709551616 (by decide)))

def checkedGate0262 : Gate := ⟨⟨0, 0, 0⟩, ⟨36893488147419103232, 0, 36893488147419103232⟩, ⟨36893488147419103232, 0, 36893488147419103232⟩⟩
theorem checkedGate0262_join : GateValid checkedGate0262 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0263 : Gate := ⟨⟨36893488147419103232, 0, 36893488147419103232⟩, ⟨36893488147419103232, 0, 36893488147419103232⟩, ⟨73786976294838206464, 0, 73786976294838206464⟩⟩
theorem checkedGate0263_join : GateValid checkedGate0263 := by
  exact Exists.intro 0 (Exists.intro 36893488147419103232 (Exists.intro 0 (by decide)))

def checkedGate0264 : Gate := ⟨⟨0, 0, 0⟩, ⟨36893488147419103232, 36893488147419103232, 0⟩, ⟨36893488147419103232, 36893488147419103232, 0⟩⟩
theorem checkedGate0264_join : GateValid checkedGate0264 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 36893488147419103232 (by decide)))

def checkedGate0265 : Gate := ⟨⟨36893488147419103232, 36893488147419103232, 0⟩, ⟨36893488147419103232, 36893488147419103232, 0⟩, ⟨73786976294838206464, 73786976294838206464, 0⟩⟩
theorem checkedGate0265_join : GateValid checkedGate0265 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 36893488147419103232 (by decide)))

def checkedGate0266 : Gate := ⟨⟨0, 0, 0⟩, ⟨73786976294838206464, 0, 73786976294838206464⟩, ⟨73786976294838206464, 0, 73786976294838206464⟩⟩
theorem checkedGate0266_join : GateValid checkedGate0266 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0267 : Gate := ⟨⟨73786976294838206464, 0, 73786976294838206464⟩, ⟨73786976294838206464, 0, 73786976294838206464⟩, ⟨147573952589676412928, 0, 147573952589676412928⟩⟩
theorem checkedGate0267_join : GateValid checkedGate0267 := by
  exact Exists.intro 0 (Exists.intro 73786976294838206464 (Exists.intro 0 (by decide)))

def checkedGate0268 : Gate := ⟨⟨0, 0, 0⟩, ⟨73786976294838206464, 73786976294838206464, 0⟩, ⟨73786976294838206464, 73786976294838206464, 0⟩⟩
theorem checkedGate0268_join : GateValid checkedGate0268 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 73786976294838206464 (by decide)))

def checkedGate0269 : Gate := ⟨⟨73786976294838206464, 73786976294838206464, 0⟩, ⟨73786976294838206464, 73786976294838206464, 0⟩, ⟨147573952589676412928, 147573952589676412928, 0⟩⟩
theorem checkedGate0269_join : GateValid checkedGate0269 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 73786976294838206464 (by decide)))

def checkedGate0270 : Gate := ⟨⟨0, 0, 0⟩, ⟨147573952589676412928, 0, 147573952589676412928⟩, ⟨147573952589676412928, 0, 147573952589676412928⟩⟩
theorem checkedGate0270_join : GateValid checkedGate0270 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0271 : Gate := ⟨⟨147573952589676412928, 0, 147573952589676412928⟩, ⟨147573952589676412928, 0, 147573952589676412928⟩, ⟨295147905179352825856, 0, 295147905179352825856⟩⟩
theorem checkedGate0271_join : GateValid checkedGate0271 := by
  exact Exists.intro 0 (Exists.intro 147573952589676412928 (Exists.intro 0 (by decide)))

def checkedGate0272 : Gate := ⟨⟨0, 0, 0⟩, ⟨147573952589676412928, 147573952589676412928, 0⟩, ⟨147573952589676412928, 147573952589676412928, 0⟩⟩
theorem checkedGate0272_join : GateValid checkedGate0272 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 147573952589676412928 (by decide)))

def checkedGate0273 : Gate := ⟨⟨147573952589676412928, 147573952589676412928, 0⟩, ⟨147573952589676412928, 147573952589676412928, 0⟩, ⟨295147905179352825856, 295147905179352825856, 0⟩⟩
theorem checkedGate0273_join : GateValid checkedGate0273 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 147573952589676412928 (by decide)))

def checkedGate0274 : Gate := ⟨⟨0, 0, 0⟩, ⟨295147905179352825856, 0, 295147905179352825856⟩, ⟨295147905179352825856, 0, 295147905179352825856⟩⟩
theorem checkedGate0274_join : GateValid checkedGate0274 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0275 : Gate := ⟨⟨295147905179352825856, 0, 295147905179352825856⟩, ⟨295147905179352825856, 0, 295147905179352825856⟩, ⟨590295810358705651712, 0, 590295810358705651712⟩⟩
theorem checkedGate0275_join : GateValid checkedGate0275 := by
  exact Exists.intro 0 (Exists.intro 295147905179352825856 (Exists.intro 0 (by decide)))

def checkedGate0276 : Gate := ⟨⟨0, 0, 0⟩, ⟨295147905179352825856, 295147905179352825856, 0⟩, ⟨295147905179352825856, 295147905179352825856, 0⟩⟩
theorem checkedGate0276_join : GateValid checkedGate0276 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 295147905179352825856 (by decide)))

def checkedGate0277 : Gate := ⟨⟨295147905179352825856, 295147905179352825856, 0⟩, ⟨295147905179352825856, 295147905179352825856, 0⟩, ⟨590295810358705651712, 590295810358705651712, 0⟩⟩
theorem checkedGate0277_join : GateValid checkedGate0277 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 295147905179352825856 (by decide)))

def checkedGate0278 : Gate := ⟨⟨0, 0, 0⟩, ⟨590295810358705651712, 0, 590295810358705651712⟩, ⟨590295810358705651712, 0, 590295810358705651712⟩⟩
theorem checkedGate0278_join : GateValid checkedGate0278 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0279 : Gate := ⟨⟨590295810358705651712, 0, 590295810358705651712⟩, ⟨590295810358705651712, 0, 590295810358705651712⟩, ⟨1180591620717411303424, 0, 1180591620717411303424⟩⟩
theorem checkedGate0279_join : GateValid checkedGate0279 := by
  exact Exists.intro 0 (Exists.intro 590295810358705651712 (Exists.intro 0 (by decide)))

def checkedGate0280 : Gate := ⟨⟨0, 0, 0⟩, ⟨590295810358705651712, 590295810358705651712, 0⟩, ⟨590295810358705651712, 590295810358705651712, 0⟩⟩
theorem checkedGate0280_join : GateValid checkedGate0280 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 590295810358705651712 (by decide)))

def checkedGate0281 : Gate := ⟨⟨590295810358705651712, 590295810358705651712, 0⟩, ⟨590295810358705651712, 590295810358705651712, 0⟩, ⟨1180591620717411303424, 1180591620717411303424, 0⟩⟩
theorem checkedGate0281_join : GateValid checkedGate0281 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 590295810358705651712 (by decide)))

def checkedGate0282 : Gate := ⟨⟨0, 0, 0⟩, ⟨1180591620717411303424, 0, 1180591620717411303424⟩, ⟨1180591620717411303424, 0, 1180591620717411303424⟩⟩
theorem checkedGate0282_join : GateValid checkedGate0282 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0283 : Gate := ⟨⟨1180591620717411303424, 0, 1180591620717411303424⟩, ⟨1180591620717411303424, 0, 1180591620717411303424⟩, ⟨2361183241434822606848, 0, 2361183241434822606848⟩⟩
theorem checkedGate0283_join : GateValid checkedGate0283 := by
  exact Exists.intro 0 (Exists.intro 1180591620717411303424 (Exists.intro 0 (by decide)))

def checkedGate0284 : Gate := ⟨⟨0, 0, 0⟩, ⟨1180591620717411303424, 1180591620717411303424, 0⟩, ⟨1180591620717411303424, 1180591620717411303424, 0⟩⟩
theorem checkedGate0284_join : GateValid checkedGate0284 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1180591620717411303424 (by decide)))

def checkedGate0285 : Gate := ⟨⟨1180591620717411303424, 1180591620717411303424, 0⟩, ⟨1180591620717411303424, 1180591620717411303424, 0⟩, ⟨2361183241434822606848, 2361183241434822606848, 0⟩⟩
theorem checkedGate0285_join : GateValid checkedGate0285 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1180591620717411303424 (by decide)))

def checkedGate0286 : Gate := ⟨⟨0, 0, 0⟩, ⟨2361183241434822606848, 0, 2361183241434822606848⟩, ⟨2361183241434822606848, 0, 2361183241434822606848⟩⟩
theorem checkedGate0286_join : GateValid checkedGate0286 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0287 : Gate := ⟨⟨2361183241434822606848, 0, 2361183241434822606848⟩, ⟨2361183241434822606848, 0, 2361183241434822606848⟩, ⟨4722366482869645213696, 0, 4722366482869645213696⟩⟩
theorem checkedGate0287_join : GateValid checkedGate0287 := by
  exact Exists.intro 0 (Exists.intro 2361183241434822606848 (Exists.intro 0 (by decide)))

def checkedGate0288 : Gate := ⟨⟨0, 0, 0⟩, ⟨2361183241434822606848, 2361183241434822606848, 0⟩, ⟨2361183241434822606848, 2361183241434822606848, 0⟩⟩
theorem checkedGate0288_join : GateValid checkedGate0288 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2361183241434822606848 (by decide)))

def checkedGate0289 : Gate := ⟨⟨2361183241434822606848, 2361183241434822606848, 0⟩, ⟨2361183241434822606848, 2361183241434822606848, 0⟩, ⟨4722366482869645213696, 4722366482869645213696, 0⟩⟩
theorem checkedGate0289_join : GateValid checkedGate0289 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2361183241434822606848 (by decide)))

def checkedGate0290 : Gate := ⟨⟨0, 0, 0⟩, ⟨4722366482869645213696, 0, 4722366482869645213696⟩, ⟨4722366482869645213696, 0, 4722366482869645213696⟩⟩
theorem checkedGate0290_join : GateValid checkedGate0290 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0291 : Gate := ⟨⟨4722366482869645213696, 0, 4722366482869645213696⟩, ⟨4722366482869645213696, 0, 4722366482869645213696⟩, ⟨9444732965739290427392, 0, 9444732965739290427392⟩⟩
theorem checkedGate0291_join : GateValid checkedGate0291 := by
  exact Exists.intro 0 (Exists.intro 4722366482869645213696 (Exists.intro 0 (by decide)))

def checkedGate0292 : Gate := ⟨⟨0, 0, 0⟩, ⟨4722366482869645213696, 4722366482869645213696, 0⟩, ⟨4722366482869645213696, 4722366482869645213696, 0⟩⟩
theorem checkedGate0292_join : GateValid checkedGate0292 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4722366482869645213696 (by decide)))

def checkedGate0293 : Gate := ⟨⟨4722366482869645213696, 4722366482869645213696, 0⟩, ⟨4722366482869645213696, 4722366482869645213696, 0⟩, ⟨9444732965739290427392, 9444732965739290427392, 0⟩⟩
theorem checkedGate0293_join : GateValid checkedGate0293 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4722366482869645213696 (by decide)))

def checkedGate0294 : Gate := ⟨⟨0, 0, 0⟩, ⟨9444732965739290427392, 0, 9444732965739290427392⟩, ⟨9444732965739290427392, 0, 9444732965739290427392⟩⟩
theorem checkedGate0294_join : GateValid checkedGate0294 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0295 : Gate := ⟨⟨9444732965739290427392, 0, 9444732965739290427392⟩, ⟨9444732965739290427392, 0, 9444732965739290427392⟩, ⟨18889465931478580854784, 0, 18889465931478580854784⟩⟩
theorem checkedGate0295_join : GateValid checkedGate0295 := by
  exact Exists.intro 0 (Exists.intro 9444732965739290427392 (Exists.intro 0 (by decide)))

def checkedGate0296 : Gate := ⟨⟨0, 0, 0⟩, ⟨9444732965739290427392, 9444732965739290427392, 0⟩, ⟨9444732965739290427392, 9444732965739290427392, 0⟩⟩
theorem checkedGate0296_join : GateValid checkedGate0296 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 9444732965739290427392 (by decide)))

def checkedGate0297 : Gate := ⟨⟨9444732965739290427392, 9444732965739290427392, 0⟩, ⟨9444732965739290427392, 9444732965739290427392, 0⟩, ⟨18889465931478580854784, 18889465931478580854784, 0⟩⟩
theorem checkedGate0297_join : GateValid checkedGate0297 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 9444732965739290427392 (by decide)))

def checkedGate0298 : Gate := ⟨⟨0, 0, 0⟩, ⟨18889465931478580854784, 0, 18889465931478580854784⟩, ⟨18889465931478580854784, 0, 18889465931478580854784⟩⟩
theorem checkedGate0298_join : GateValid checkedGate0298 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0299 : Gate := ⟨⟨18889465931478580854784, 0, 18889465931478580854784⟩, ⟨18889465931478580854784, 0, 18889465931478580854784⟩, ⟨37778931862957161709568, 0, 37778931862957161709568⟩⟩
theorem checkedGate0299_join : GateValid checkedGate0299 := by
  exact Exists.intro 0 (Exists.intro 18889465931478580854784 (Exists.intro 0 (by decide)))

def checkedGate0300 : Gate := ⟨⟨0, 0, 0⟩, ⟨18889465931478580854784, 18889465931478580854784, 0⟩, ⟨18889465931478580854784, 18889465931478580854784, 0⟩⟩
theorem checkedGate0300_join : GateValid checkedGate0300 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 18889465931478580854784 (by decide)))

def checkedGate0301 : Gate := ⟨⟨18889465931478580854784, 18889465931478580854784, 0⟩, ⟨18889465931478580854784, 18889465931478580854784, 0⟩, ⟨37778931862957161709568, 37778931862957161709568, 0⟩⟩
theorem checkedGate0301_join : GateValid checkedGate0301 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 18889465931478580854784 (by decide)))

def checkedGate0302 : Gate := ⟨⟨0, 0, 0⟩, ⟨37778931862957161709568, 0, 37778931862957161709568⟩, ⟨37778931862957161709568, 0, 37778931862957161709568⟩⟩
theorem checkedGate0302_join : GateValid checkedGate0302 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0303 : Gate := ⟨⟨37778931862957161709568, 0, 37778931862957161709568⟩, ⟨37778931862957161709568, 0, 37778931862957161709568⟩, ⟨75557863725914323419136, 0, 75557863725914323419136⟩⟩
theorem checkedGate0303_join : GateValid checkedGate0303 := by
  exact Exists.intro 0 (Exists.intro 37778931862957161709568 (Exists.intro 0 (by decide)))

def checkedGate0304 : Gate := ⟨⟨0, 0, 0⟩, ⟨37778931862957161709568, 37778931862957161709568, 0⟩, ⟨37778931862957161709568, 37778931862957161709568, 0⟩⟩
theorem checkedGate0304_join : GateValid checkedGate0304 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 37778931862957161709568 (by decide)))

def checkedGate0305 : Gate := ⟨⟨37778931862957161709568, 37778931862957161709568, 0⟩, ⟨37778931862957161709568, 37778931862957161709568, 0⟩, ⟨75557863725914323419136, 75557863725914323419136, 0⟩⟩
theorem checkedGate0305_join : GateValid checkedGate0305 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 37778931862957161709568 (by decide)))

def checkedGate0306 : Gate := ⟨⟨0, 0, 0⟩, ⟨75557863725914323419136, 0, 75557863725914323419136⟩, ⟨75557863725914323419136, 0, 75557863725914323419136⟩⟩
theorem checkedGate0306_join : GateValid checkedGate0306 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0307 : Gate := ⟨⟨75557863725914323419136, 0, 75557863725914323419136⟩, ⟨75557863725914323419136, 0, 75557863725914323419136⟩, ⟨151115727451828646838272, 0, 151115727451828646838272⟩⟩
theorem checkedGate0307_join : GateValid checkedGate0307 := by
  exact Exists.intro 0 (Exists.intro 75557863725914323419136 (Exists.intro 0 (by decide)))

def checkedGate0308 : Gate := ⟨⟨0, 0, 0⟩, ⟨75557863725914323419136, 75557863725914323419136, 0⟩, ⟨75557863725914323419136, 75557863725914323419136, 0⟩⟩
theorem checkedGate0308_join : GateValid checkedGate0308 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 75557863725914323419136 (by decide)))

def checkedGate0309 : Gate := ⟨⟨75557863725914323419136, 75557863725914323419136, 0⟩, ⟨75557863725914323419136, 75557863725914323419136, 0⟩, ⟨151115727451828646838272, 151115727451828646838272, 0⟩⟩
theorem checkedGate0309_join : GateValid checkedGate0309 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 75557863725914323419136 (by decide)))

def checkedGate0310 : Gate := ⟨⟨0, 0, 0⟩, ⟨151115727451828646838272, 0, 151115727451828646838272⟩, ⟨151115727451828646838272, 0, 151115727451828646838272⟩⟩
theorem checkedGate0310_join : GateValid checkedGate0310 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0311 : Gate := ⟨⟨151115727451828646838272, 0, 151115727451828646838272⟩, ⟨151115727451828646838272, 0, 151115727451828646838272⟩, ⟨302231454903657293676544, 0, 302231454903657293676544⟩⟩
theorem checkedGate0311_join : GateValid checkedGate0311 := by
  exact Exists.intro 0 (Exists.intro 151115727451828646838272 (Exists.intro 0 (by decide)))

def checkedGate0312 : Gate := ⟨⟨0, 0, 0⟩, ⟨151115727451828646838272, 151115727451828646838272, 0⟩, ⟨151115727451828646838272, 151115727451828646838272, 0⟩⟩
theorem checkedGate0312_join : GateValid checkedGate0312 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 151115727451828646838272 (by decide)))

def checkedGate0313 : Gate := ⟨⟨151115727451828646838272, 151115727451828646838272, 0⟩, ⟨151115727451828646838272, 151115727451828646838272, 0⟩, ⟨302231454903657293676544, 302231454903657293676544, 0⟩⟩
theorem checkedGate0313_join : GateValid checkedGate0313 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 151115727451828646838272 (by decide)))

def checkedGate0314 : Gate := ⟨⟨0, 0, 0⟩, ⟨302231454903657293676544, 0, 302231454903657293676544⟩, ⟨302231454903657293676544, 0, 302231454903657293676544⟩⟩
theorem checkedGate0314_join : GateValid checkedGate0314 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0315 : Gate := ⟨⟨302231454903657293676544, 0, 302231454903657293676544⟩, ⟨302231454903657293676544, 0, 302231454903657293676544⟩, ⟨604462909807314587353088, 0, 604462909807314587353088⟩⟩
theorem checkedGate0315_join : GateValid checkedGate0315 := by
  exact Exists.intro 0 (Exists.intro 302231454903657293676544 (Exists.intro 0 (by decide)))

def checkedGate0316 : Gate := ⟨⟨0, 0, 0⟩, ⟨302231454903657293676544, 302231454903657293676544, 0⟩, ⟨302231454903657293676544, 302231454903657293676544, 0⟩⟩
theorem checkedGate0316_join : GateValid checkedGate0316 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 302231454903657293676544 (by decide)))

def checkedGate0317 : Gate := ⟨⟨302231454903657293676544, 302231454903657293676544, 0⟩, ⟨302231454903657293676544, 302231454903657293676544, 0⟩, ⟨604462909807314587353088, 604462909807314587353088, 0⟩⟩
theorem checkedGate0317_join : GateValid checkedGate0317 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 302231454903657293676544 (by decide)))

def checkedGate0318 : Gate := ⟨⟨0, 0, 0⟩, ⟨604462909807314587353088, 0, 604462909807314587353088⟩, ⟨604462909807314587353088, 0, 604462909807314587353088⟩⟩
theorem checkedGate0318_join : GateValid checkedGate0318 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0319 : Gate := ⟨⟨604462909807314587353088, 0, 604462909807314587353088⟩, ⟨604462909807314587353088, 0, 604462909807314587353088⟩, ⟨1208925819614629174706176, 0, 1208925819614629174706176⟩⟩
theorem checkedGate0319_join : GateValid checkedGate0319 := by
  exact Exists.intro 0 (Exists.intro 604462909807314587353088 (Exists.intro 0 (by decide)))

def checkedGate0320 : Gate := ⟨⟨0, 0, 0⟩, ⟨604462909807314587353088, 604462909807314587353088, 0⟩, ⟨604462909807314587353088, 604462909807314587353088, 0⟩⟩
theorem checkedGate0320_join : GateValid checkedGate0320 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 604462909807314587353088 (by decide)))

def checkedGate0321 : Gate := ⟨⟨604462909807314587353088, 604462909807314587353088, 0⟩, ⟨604462909807314587353088, 604462909807314587353088, 0⟩, ⟨1208925819614629174706176, 1208925819614629174706176, 0⟩⟩
theorem checkedGate0321_join : GateValid checkedGate0321 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 604462909807314587353088 (by decide)))

def checkedGate0322 : Gate := ⟨⟨0, 0, 0⟩, ⟨1208925819614629174706176, 0, 1208925819614629174706176⟩, ⟨1208925819614629174706176, 0, 1208925819614629174706176⟩⟩
theorem checkedGate0322_join : GateValid checkedGate0322 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0323 : Gate := ⟨⟨1208925819614629174706176, 0, 1208925819614629174706176⟩, ⟨1208925819614629174706176, 0, 1208925819614629174706176⟩, ⟨2417851639229258349412352, 0, 2417851639229258349412352⟩⟩
theorem checkedGate0323_join : GateValid checkedGate0323 := by
  exact Exists.intro 0 (Exists.intro 1208925819614629174706176 (Exists.intro 0 (by decide)))

def checkedGate0324 : Gate := ⟨⟨0, 0, 0⟩, ⟨1208925819614629174706176, 1208925819614629174706176, 0⟩, ⟨1208925819614629174706176, 1208925819614629174706176, 0⟩⟩
theorem checkedGate0324_join : GateValid checkedGate0324 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1208925819614629174706176 (by decide)))

def checkedGate0325 : Gate := ⟨⟨1208925819614629174706176, 1208925819614629174706176, 0⟩, ⟨1208925819614629174706176, 1208925819614629174706176, 0⟩, ⟨2417851639229258349412352, 2417851639229258349412352, 0⟩⟩
theorem checkedGate0325_join : GateValid checkedGate0325 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1208925819614629174706176 (by decide)))

def checkedGate0326 : Gate := ⟨⟨0, 0, 0⟩, ⟨2417851639229258349412352, 0, 2417851639229258349412352⟩, ⟨2417851639229258349412352, 0, 2417851639229258349412352⟩⟩
theorem checkedGate0326_join : GateValid checkedGate0326 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0327 : Gate := ⟨⟨2417851639229258349412352, 0, 2417851639229258349412352⟩, ⟨2417851639229258349412352, 0, 2417851639229258349412352⟩, ⟨4835703278458516698824704, 0, 4835703278458516698824704⟩⟩
theorem checkedGate0327_join : GateValid checkedGate0327 := by
  exact Exists.intro 0 (Exists.intro 2417851639229258349412352 (Exists.intro 0 (by decide)))

def checkedGate0328 : Gate := ⟨⟨0, 0, 0⟩, ⟨2417851639229258349412352, 2417851639229258349412352, 0⟩, ⟨2417851639229258349412352, 2417851639229258349412352, 0⟩⟩
theorem checkedGate0328_join : GateValid checkedGate0328 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2417851639229258349412352 (by decide)))

def checkedGate0329 : Gate := ⟨⟨2417851639229258349412352, 2417851639229258349412352, 0⟩, ⟨2417851639229258349412352, 2417851639229258349412352, 0⟩, ⟨4835703278458516698824704, 4835703278458516698824704, 0⟩⟩
theorem checkedGate0329_join : GateValid checkedGate0329 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2417851639229258349412352 (by decide)))

def checkedGate0330 : Gate := ⟨⟨0, 0, 0⟩, ⟨4835703278458516698824704, 0, 4835703278458516698824704⟩, ⟨4835703278458516698824704, 0, 4835703278458516698824704⟩⟩
theorem checkedGate0330_join : GateValid checkedGate0330 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0331 : Gate := ⟨⟨4835703278458516698824704, 0, 4835703278458516698824704⟩, ⟨4835703278458516698824704, 0, 4835703278458516698824704⟩, ⟨9671406556917033397649408, 0, 9671406556917033397649408⟩⟩
theorem checkedGate0331_join : GateValid checkedGate0331 := by
  exact Exists.intro 0 (Exists.intro 4835703278458516698824704 (Exists.intro 0 (by decide)))

def checkedGate0332 : Gate := ⟨⟨0, 0, 0⟩, ⟨4835703278458516698824704, 4835703278458516698824704, 0⟩, ⟨4835703278458516698824704, 4835703278458516698824704, 0⟩⟩
theorem checkedGate0332_join : GateValid checkedGate0332 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4835703278458516698824704 (by decide)))

def checkedGate0333 : Gate := ⟨⟨4835703278458516698824704, 4835703278458516698824704, 0⟩, ⟨4835703278458516698824704, 4835703278458516698824704, 0⟩, ⟨9671406556917033397649408, 9671406556917033397649408, 0⟩⟩
theorem checkedGate0333_join : GateValid checkedGate0333 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4835703278458516698824704 (by decide)))

def checkedGate0334 : Gate := ⟨⟨0, 0, 0⟩, ⟨9671406556917033397649408, 0, 9671406556917033397649408⟩, ⟨9671406556917033397649408, 0, 9671406556917033397649408⟩⟩
theorem checkedGate0334_join : GateValid checkedGate0334 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0335 : Gate := ⟨⟨9671406556917033397649408, 0, 9671406556917033397649408⟩, ⟨9671406556917033397649408, 0, 9671406556917033397649408⟩, ⟨19342813113834066795298816, 0, 19342813113834066795298816⟩⟩
theorem checkedGate0335_join : GateValid checkedGate0335 := by
  exact Exists.intro 0 (Exists.intro 9671406556917033397649408 (Exists.intro 0 (by decide)))

def checkedGate0336 : Gate := ⟨⟨0, 0, 0⟩, ⟨9671406556917033397649408, 9671406556917033397649408, 0⟩, ⟨9671406556917033397649408, 9671406556917033397649408, 0⟩⟩
theorem checkedGate0336_join : GateValid checkedGate0336 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 9671406556917033397649408 (by decide)))

def checkedGate0337 : Gate := ⟨⟨9671406556917033397649408, 9671406556917033397649408, 0⟩, ⟨9671406556917033397649408, 9671406556917033397649408, 0⟩, ⟨19342813113834066795298816, 19342813113834066795298816, 0⟩⟩
theorem checkedGate0337_join : GateValid checkedGate0337 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 9671406556917033397649408 (by decide)))

def checkedGate0338 : Gate := ⟨⟨0, 0, 0⟩, ⟨19342813113834066795298816, 0, 19342813113834066795298816⟩, ⟨19342813113834066795298816, 0, 19342813113834066795298816⟩⟩
theorem checkedGate0338_join : GateValid checkedGate0338 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0339 : Gate := ⟨⟨19342813113834066795298816, 0, 19342813113834066795298816⟩, ⟨19342813113834066795298816, 0, 19342813113834066795298816⟩, ⟨38685626227668133590597632, 0, 38685626227668133590597632⟩⟩
theorem checkedGate0339_join : GateValid checkedGate0339 := by
  exact Exists.intro 0 (Exists.intro 19342813113834066795298816 (Exists.intro 0 (by decide)))

def checkedGate0340 : Gate := ⟨⟨0, 0, 0⟩, ⟨19342813113834066795298816, 19342813113834066795298816, 0⟩, ⟨19342813113834066795298816, 19342813113834066795298816, 0⟩⟩
theorem checkedGate0340_join : GateValid checkedGate0340 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 19342813113834066795298816 (by decide)))

def checkedGate0341 : Gate := ⟨⟨19342813113834066795298816, 19342813113834066795298816, 0⟩, ⟨19342813113834066795298816, 19342813113834066795298816, 0⟩, ⟨38685626227668133590597632, 38685626227668133590597632, 0⟩⟩
theorem checkedGate0341_join : GateValid checkedGate0341 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 19342813113834066795298816 (by decide)))

def checkedGate0342 : Gate := ⟨⟨0, 0, 0⟩, ⟨38685626227668133590597632, 0, 38685626227668133590597632⟩, ⟨38685626227668133590597632, 0, 38685626227668133590597632⟩⟩
theorem checkedGate0342_join : GateValid checkedGate0342 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0343 : Gate := ⟨⟨38685626227668133590597632, 0, 38685626227668133590597632⟩, ⟨38685626227668133590597632, 0, 38685626227668133590597632⟩, ⟨77371252455336267181195264, 0, 77371252455336267181195264⟩⟩
theorem checkedGate0343_join : GateValid checkedGate0343 := by
  exact Exists.intro 0 (Exists.intro 38685626227668133590597632 (Exists.intro 0 (by decide)))

def checkedGate0344 : Gate := ⟨⟨0, 0, 0⟩, ⟨38685626227668133590597632, 38685626227668133590597632, 0⟩, ⟨38685626227668133590597632, 38685626227668133590597632, 0⟩⟩
theorem checkedGate0344_join : GateValid checkedGate0344 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 38685626227668133590597632 (by decide)))

def checkedGate0345 : Gate := ⟨⟨38685626227668133590597632, 38685626227668133590597632, 0⟩, ⟨38685626227668133590597632, 38685626227668133590597632, 0⟩, ⟨77371252455336267181195264, 77371252455336267181195264, 0⟩⟩
theorem checkedGate0345_join : GateValid checkedGate0345 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 38685626227668133590597632 (by decide)))

def checkedGate0346 : Gate := ⟨⟨0, 0, 0⟩, ⟨77371252455336267181195264, 0, 77371252455336267181195264⟩, ⟨77371252455336267181195264, 0, 77371252455336267181195264⟩⟩
theorem checkedGate0346_join : GateValid checkedGate0346 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0347 : Gate := ⟨⟨77371252455336267181195264, 0, 77371252455336267181195264⟩, ⟨77371252455336267181195264, 0, 77371252455336267181195264⟩, ⟨154742504910672534362390528, 0, 154742504910672534362390528⟩⟩
theorem checkedGate0347_join : GateValid checkedGate0347 := by
  exact Exists.intro 0 (Exists.intro 77371252455336267181195264 (Exists.intro 0 (by decide)))

def checkedGate0348 : Gate := ⟨⟨0, 0, 0⟩, ⟨77371252455336267181195264, 77371252455336267181195264, 0⟩, ⟨77371252455336267181195264, 77371252455336267181195264, 0⟩⟩
theorem checkedGate0348_join : GateValid checkedGate0348 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 77371252455336267181195264 (by decide)))

def checkedGate0349 : Gate := ⟨⟨77371252455336267181195264, 77371252455336267181195264, 0⟩, ⟨77371252455336267181195264, 77371252455336267181195264, 0⟩, ⟨154742504910672534362390528, 154742504910672534362390528, 0⟩⟩
theorem checkedGate0349_join : GateValid checkedGate0349 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 77371252455336267181195264 (by decide)))

def checkedGate0350 : Gate := ⟨⟨0, 0, 0⟩, ⟨154742504910672534362390528, 0, 154742504910672534362390528⟩, ⟨154742504910672534362390528, 0, 154742504910672534362390528⟩⟩
theorem checkedGate0350_join : GateValid checkedGate0350 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0351 : Gate := ⟨⟨154742504910672534362390528, 0, 154742504910672534362390528⟩, ⟨154742504910672534362390528, 0, 154742504910672534362390528⟩, ⟨309485009821345068724781056, 0, 309485009821345068724781056⟩⟩
theorem checkedGate0351_join : GateValid checkedGate0351 := by
  exact Exists.intro 0 (Exists.intro 154742504910672534362390528 (Exists.intro 0 (by decide)))

def checkedGate0352 : Gate := ⟨⟨0, 0, 0⟩, ⟨154742504910672534362390528, 154742504910672534362390528, 0⟩, ⟨154742504910672534362390528, 154742504910672534362390528, 0⟩⟩
theorem checkedGate0352_join : GateValid checkedGate0352 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 154742504910672534362390528 (by decide)))

def checkedGate0353 : Gate := ⟨⟨154742504910672534362390528, 154742504910672534362390528, 0⟩, ⟨154742504910672534362390528, 154742504910672534362390528, 0⟩, ⟨309485009821345068724781056, 309485009821345068724781056, 0⟩⟩
theorem checkedGate0353_join : GateValid checkedGate0353 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 154742504910672534362390528 (by decide)))

def checkedGate0354 : Gate := ⟨⟨0, 0, 0⟩, ⟨309485009821345068724781056, 0, 309485009821345068724781056⟩, ⟨309485009821345068724781056, 0, 309485009821345068724781056⟩⟩
theorem checkedGate0354_join : GateValid checkedGate0354 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0355 : Gate := ⟨⟨309485009821345068724781056, 0, 309485009821345068724781056⟩, ⟨309485009821345068724781056, 0, 309485009821345068724781056⟩, ⟨618970019642690137449562112, 0, 618970019642690137449562112⟩⟩
theorem checkedGate0355_join : GateValid checkedGate0355 := by
  exact Exists.intro 0 (Exists.intro 309485009821345068724781056 (Exists.intro 0 (by decide)))

def checkedGate0356 : Gate := ⟨⟨0, 0, 0⟩, ⟨309485009821345068724781056, 309485009821345068724781056, 0⟩, ⟨309485009821345068724781056, 309485009821345068724781056, 0⟩⟩
theorem checkedGate0356_join : GateValid checkedGate0356 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 309485009821345068724781056 (by decide)))

def checkedGate0357 : Gate := ⟨⟨309485009821345068724781056, 309485009821345068724781056, 0⟩, ⟨309485009821345068724781056, 309485009821345068724781056, 0⟩, ⟨618970019642690137449562112, 618970019642690137449562112, 0⟩⟩
theorem checkedGate0357_join : GateValid checkedGate0357 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 309485009821345068724781056 (by decide)))

def checkedGate0358 : Gate := ⟨⟨0, 0, 0⟩, ⟨618970019642690137449562112, 0, 618970019642690137449562112⟩, ⟨618970019642690137449562112, 0, 618970019642690137449562112⟩⟩
theorem checkedGate0358_join : GateValid checkedGate0358 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0359 : Gate := ⟨⟨618970019642690137449562112, 0, 618970019642690137449562112⟩, ⟨618970019642690137449562112, 0, 618970019642690137449562112⟩, ⟨1237940039285380274899124224, 0, 1237940039285380274899124224⟩⟩
theorem checkedGate0359_join : GateValid checkedGate0359 := by
  exact Exists.intro 0 (Exists.intro 618970019642690137449562112 (Exists.intro 0 (by decide)))

def checkedGate0360 : Gate := ⟨⟨0, 0, 0⟩, ⟨618970019642690137449562112, 618970019642690137449562112, 0⟩, ⟨618970019642690137449562112, 618970019642690137449562112, 0⟩⟩
theorem checkedGate0360_join : GateValid checkedGate0360 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 618970019642690137449562112 (by decide)))

def checkedGate0361 : Gate := ⟨⟨618970019642690137449562112, 618970019642690137449562112, 0⟩, ⟨618970019642690137449562112, 618970019642690137449562112, 0⟩, ⟨1237940039285380274899124224, 1237940039285380274899124224, 0⟩⟩
theorem checkedGate0361_join : GateValid checkedGate0361 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 618970019642690137449562112 (by decide)))

def checkedGate0362 : Gate := ⟨⟨0, 0, 0⟩, ⟨1237940039285380274899124224, 0, 1237940039285380274899124224⟩, ⟨1237940039285380274899124224, 0, 1237940039285380274899124224⟩⟩
theorem checkedGate0362_join : GateValid checkedGate0362 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0363 : Gate := ⟨⟨1237940039285380274899124224, 0, 1237940039285380274899124224⟩, ⟨1237940039285380274899124224, 0, 1237940039285380274899124224⟩, ⟨2475880078570760549798248448, 0, 2475880078570760549798248448⟩⟩
theorem checkedGate0363_join : GateValid checkedGate0363 := by
  exact Exists.intro 0 (Exists.intro 1237940039285380274899124224 (Exists.intro 0 (by decide)))

def checkedGate0364 : Gate := ⟨⟨0, 0, 0⟩, ⟨1237940039285380274899124224, 1237940039285380274899124224, 0⟩, ⟨1237940039285380274899124224, 1237940039285380274899124224, 0⟩⟩
theorem checkedGate0364_join : GateValid checkedGate0364 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1237940039285380274899124224 (by decide)))

def checkedGate0365 : Gate := ⟨⟨1237940039285380274899124224, 1237940039285380274899124224, 0⟩, ⟨1237940039285380274899124224, 1237940039285380274899124224, 0⟩, ⟨2475880078570760549798248448, 2475880078570760549798248448, 0⟩⟩
theorem checkedGate0365_join : GateValid checkedGate0365 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 1237940039285380274899124224 (by decide)))

def checkedGate0366 : Gate := ⟨⟨0, 0, 0⟩, ⟨2475880078570760549798248448, 0, 2475880078570760549798248448⟩, ⟨2475880078570760549798248448, 0, 2475880078570760549798248448⟩⟩
theorem checkedGate0366_join : GateValid checkedGate0366 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0367 : Gate := ⟨⟨2475880078570760549798248448, 0, 2475880078570760549798248448⟩, ⟨2475880078570760549798248448, 0, 2475880078570760549798248448⟩, ⟨4951760157141521099596496896, 0, 4951760157141521099596496896⟩⟩
theorem checkedGate0367_join : GateValid checkedGate0367 := by
  exact Exists.intro 0 (Exists.intro 2475880078570760549798248448 (Exists.intro 0 (by decide)))

def checkedGate0368 : Gate := ⟨⟨0, 0, 0⟩, ⟨2475880078570760549798248448, 2475880078570760549798248448, 0⟩, ⟨2475880078570760549798248448, 2475880078570760549798248448, 0⟩⟩
theorem checkedGate0368_join : GateValid checkedGate0368 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2475880078570760549798248448 (by decide)))

def checkedGate0369 : Gate := ⟨⟨2475880078570760549798248448, 2475880078570760549798248448, 0⟩, ⟨2475880078570760549798248448, 2475880078570760549798248448, 0⟩, ⟨4951760157141521099596496896, 4951760157141521099596496896, 0⟩⟩
theorem checkedGate0369_join : GateValid checkedGate0369 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 2475880078570760549798248448 (by decide)))

def checkedGate0370 : Gate := ⟨⟨0, 0, 0⟩, ⟨4951760157141521099596496896, 0, 4951760157141521099596496896⟩, ⟨4951760157141521099596496896, 0, 4951760157141521099596496896⟩⟩
theorem checkedGate0370_join : GateValid checkedGate0370 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0371 : Gate := ⟨⟨4951760157141521099596496896, 0, 4951760157141521099596496896⟩, ⟨4951760157141521099596496896, 0, 4951760157141521099596496896⟩, ⟨9903520314283042199192993792, 0, 9903520314283042199192993792⟩⟩
theorem checkedGate0371_join : GateValid checkedGate0371 := by
  exact Exists.intro 0 (Exists.intro 4951760157141521099596496896 (Exists.intro 0 (by decide)))

def checkedGate0372 : Gate := ⟨⟨0, 0, 0⟩, ⟨4951760157141521099596496896, 4951760157141521099596496896, 0⟩, ⟨4951760157141521099596496896, 4951760157141521099596496896, 0⟩⟩
theorem checkedGate0372_join : GateValid checkedGate0372 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4951760157141521099596496896 (by decide)))

def checkedGate0373 : Gate := ⟨⟨4951760157141521099596496896, 4951760157141521099596496896, 0⟩, ⟨4951760157141521099596496896, 4951760157141521099596496896, 0⟩, ⟨9903520314283042199192993792, 9903520314283042199192993792, 0⟩⟩
theorem checkedGate0373_join : GateValid checkedGate0373 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 4951760157141521099596496896 (by decide)))

def checkedGate0374 : Gate := ⟨⟨0, 0, 0⟩, ⟨9903520314283042199192993792, 0, 9903520314283042199192993792⟩, ⟨9903520314283042199192993792, 0, 9903520314283042199192993792⟩⟩
theorem checkedGate0374_join : GateValid checkedGate0374 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0375 : Gate := ⟨⟨9903520314283042199192993792, 0, 9903520314283042199192993792⟩, ⟨9903520314283042199192993792, 0, 9903520314283042199192993792⟩, ⟨19807040628566084398385987584, 0, 19807040628566084398385987584⟩⟩
theorem checkedGate0375_join : GateValid checkedGate0375 := by
  exact Exists.intro 0 (Exists.intro 9903520314283042199192993792 (Exists.intro 0 (by decide)))

def checkedGate0376 : Gate := ⟨⟨0, 0, 0⟩, ⟨9903520314283042199192993792, 9903520314283042199192993792, 0⟩, ⟨9903520314283042199192993792, 9903520314283042199192993792, 0⟩⟩
theorem checkedGate0376_join : GateValid checkedGate0376 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 9903520314283042199192993792 (by decide)))

def checkedGate0377 : Gate := ⟨⟨9903520314283042199192993792, 9903520314283042199192993792, 0⟩, ⟨9903520314283042199192993792, 9903520314283042199192993792, 0⟩, ⟨19807040628566084398385987584, 19807040628566084398385987584, 0⟩⟩
theorem checkedGate0377_join : GateValid checkedGate0377 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 9903520314283042199192993792 (by decide)))

def checkedGate0378 : Gate := ⟨⟨0, 0, 0⟩, ⟨19807040628566084398385987584, 0, 19807040628566084398385987584⟩, ⟨19807040628566084398385987584, 0, 19807040628566084398385987584⟩⟩
theorem checkedGate0378_join : GateValid checkedGate0378 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0379 : Gate := ⟨⟨19807040628566084398385987584, 0, 19807040628566084398385987584⟩, ⟨19807040628566084398385987584, 0, 19807040628566084398385987584⟩, ⟨39614081257132168796771975168, 0, 39614081257132168796771975168⟩⟩
theorem checkedGate0379_join : GateValid checkedGate0379 := by
  exact Exists.intro 0 (Exists.intro 19807040628566084398385987584 (Exists.intro 0 (by decide)))

def checkedGate0380 : Gate := ⟨⟨0, 0, 0⟩, ⟨19807040628566084398385987584, 19807040628566084398385987584, 0⟩, ⟨19807040628566084398385987584, 19807040628566084398385987584, 0⟩⟩
theorem checkedGate0380_join : GateValid checkedGate0380 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 19807040628566084398385987584 (by decide)))

def checkedGate0381 : Gate := ⟨⟨19807040628566084398385987584, 19807040628566084398385987584, 0⟩, ⟨19807040628566084398385987584, 19807040628566084398385987584, 0⟩, ⟨39614081257132168796771975168, 39614081257132168796771975168, 0⟩⟩
theorem checkedGate0381_join : GateValid checkedGate0381 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 19807040628566084398385987584 (by decide)))

def checkedGate0382 : Gate := ⟨⟨0, 0, 0⟩, ⟨39614081257132168796771975168, 0, 39614081257132168796771975168⟩, ⟨39614081257132168796771975168, 0, 39614081257132168796771975168⟩⟩
theorem checkedGate0382_join : GateValid checkedGate0382 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0383 : Gate := ⟨⟨39614081257132168796771975168, 0, 39614081257132168796771975168⟩, ⟨39614081257132168796771975168, 0, 39614081257132168796771975168⟩, ⟨79228162514264337593543950336, 0, 79228162514264337593543950336⟩⟩
theorem checkedGate0383_join : GateValid checkedGate0383 := by
  exact Exists.intro 0 (Exists.intro 39614081257132168796771975168 (Exists.intro 0 (by decide)))

def checkedGate0384 : Gate := ⟨⟨0, 0, 0⟩, ⟨39614081257132168796771975168, 39614081257132168796771975168, 0⟩, ⟨39614081257132168796771975168, 39614081257132168796771975168, 0⟩⟩
theorem checkedGate0384_join : GateValid checkedGate0384 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 39614081257132168796771975168 (by decide)))

def checkedGate0385 : Gate := ⟨⟨39614081257132168796771975168, 39614081257132168796771975168, 0⟩, ⟨39614081257132168796771975168, 39614081257132168796771975168, 0⟩, ⟨79228162514264337593543950336, 79228162514264337593543950336, 0⟩⟩
theorem checkedGate0385_join : GateValid checkedGate0385 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 39614081257132168796771975168 (by decide)))

def checkedGate0386 : Gate := ⟨⟨0, 0, 0⟩, ⟨79228162514264337593543950336, 0, 79228162514264337593543950336⟩, ⟨79228162514264337593543950336, 0, 79228162514264337593543950336⟩⟩
theorem checkedGate0386_join : GateValid checkedGate0386 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0387 : Gate := ⟨⟨79228162514264337593543950336, 0, 79228162514264337593543950336⟩, ⟨79228162514264337593543950336, 0, 79228162514264337593543950336⟩, ⟨158456325028528675187087900672, 0, 158456325028528675187087900672⟩⟩
theorem checkedGate0387_join : GateValid checkedGate0387 := by
  exact Exists.intro 0 (Exists.intro 79228162514264337593543950336 (Exists.intro 0 (by decide)))

def checkedGate0388 : Gate := ⟨⟨0, 0, 0⟩, ⟨79228162514264337593543950336, 79228162514264337593543950336, 0⟩, ⟨79228162514264337593543950336, 79228162514264337593543950336, 0⟩⟩
theorem checkedGate0388_join : GateValid checkedGate0388 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 79228162514264337593543950336 (by decide)))

def checkedGate0389 : Gate := ⟨⟨79228162514264337593543950336, 79228162514264337593543950336, 0⟩, ⟨79228162514264337593543950336, 79228162514264337593543950336, 0⟩, ⟨158456325028528675187087900672, 158456325028528675187087900672, 0⟩⟩
theorem checkedGate0389_join : GateValid checkedGate0389 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 79228162514264337593543950336 (by decide)))

def checkedGate0390 : Gate := ⟨⟨0, 0, 0⟩, ⟨158456325028528675187087900672, 0, 158456325028528675187087900672⟩, ⟨158456325028528675187087900672, 0, 158456325028528675187087900672⟩⟩
theorem checkedGate0390_join : GateValid checkedGate0390 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0391 : Gate := ⟨⟨158456325028528675187087900672, 0, 158456325028528675187087900672⟩, ⟨158456325028528675187087900672, 0, 158456325028528675187087900672⟩, ⟨316912650057057350374175801344, 0, 316912650057057350374175801344⟩⟩
theorem checkedGate0391_join : GateValid checkedGate0391 := by
  exact Exists.intro 0 (Exists.intro 158456325028528675187087900672 (Exists.intro 0 (by decide)))

def checkedGate0392 : Gate := ⟨⟨0, 0, 0⟩, ⟨158456325028528675187087900672, 158456325028528675187087900672, 0⟩, ⟨158456325028528675187087900672, 158456325028528675187087900672, 0⟩⟩
theorem checkedGate0392_join : GateValid checkedGate0392 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 158456325028528675187087900672 (by decide)))

def checkedGate0393 : Gate := ⟨⟨158456325028528675187087900672, 158456325028528675187087900672, 0⟩, ⟨158456325028528675187087900672, 158456325028528675187087900672, 0⟩, ⟨316912650057057350374175801344, 316912650057057350374175801344, 0⟩⟩
theorem checkedGate0393_join : GateValid checkedGate0393 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 158456325028528675187087900672 (by decide)))

def checkedGate0394 : Gate := ⟨⟨0, 0, 0⟩, ⟨316912650057057350374175801344, 0, 316912650057057350374175801344⟩, ⟨316912650057057350374175801344, 0, 316912650057057350374175801344⟩⟩
theorem checkedGate0394_join : GateValid checkedGate0394 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0395 : Gate := ⟨⟨316912650057057350374175801344, 0, 316912650057057350374175801344⟩, ⟨316912650057057350374175801344, 0, 316912650057057350374175801344⟩, ⟨633825300114114700748351602688, 0, 633825300114114700748351602688⟩⟩
theorem checkedGate0395_join : GateValid checkedGate0395 := by
  exact Exists.intro 0 (Exists.intro 316912650057057350374175801344 (Exists.intro 0 (by decide)))

def checkedGate0396 : Gate := ⟨⟨0, 0, 0⟩, ⟨316912650057057350374175801344, 316912650057057350374175801344, 0⟩, ⟨316912650057057350374175801344, 316912650057057350374175801344, 0⟩⟩
theorem checkedGate0396_join : GateValid checkedGate0396 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 316912650057057350374175801344 (by decide)))

def checkedGate0397 : Gate := ⟨⟨316912650057057350374175801344, 316912650057057350374175801344, 0⟩, ⟨316912650057057350374175801344, 316912650057057350374175801344, 0⟩, ⟨633825300114114700748351602688, 633825300114114700748351602688, 0⟩⟩
theorem checkedGate0397_join : GateValid checkedGate0397 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 316912650057057350374175801344 (by decide)))

def checkedGate0398 : Gate := ⟨⟨0, 0, 0⟩, ⟨633825300114114700748351602688, 0, 633825300114114700748351602688⟩, ⟨633825300114114700748351602688, 0, 633825300114114700748351602688⟩⟩
theorem checkedGate0398_join : GateValid checkedGate0398 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0399 : Gate := ⟨⟨633825300114114700748351602688, 0, 633825300114114700748351602688⟩, ⟨633825300114114700748351602688, 0, 633825300114114700748351602688⟩, ⟨1267650600228229401496703205376, 0, 1267650600228229401496703205376⟩⟩
theorem checkedGate0399_join : GateValid checkedGate0399 := by
  exact Exists.intro 0 (Exists.intro 633825300114114700748351602688 (Exists.intro 0 (by decide)))

def checkedGate0400 : Gate := ⟨⟨0, 0, 0⟩, ⟨633825300114114700748351602688, 633825300114114700748351602688, 0⟩, ⟨633825300114114700748351602688, 633825300114114700748351602688, 0⟩⟩
theorem checkedGate0400_join : GateValid checkedGate0400 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 633825300114114700748351602688 (by decide)))

def checkedGate0401 : Gate := ⟨⟨633825300114114700748351602688, 633825300114114700748351602688, 0⟩, ⟨633825300114114700748351602688, 633825300114114700748351602688, 0⟩, ⟨1267650600228229401496703205376, 1267650600228229401496703205376, 0⟩⟩
theorem checkedGate0401_join : GateValid checkedGate0401 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 633825300114114700748351602688 (by decide)))

def checkedGate0402 : Gate := ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩
theorem checkedGate0402_join : GateValid checkedGate0402 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0403 : Gate := ⟨⟨0, 0, 0⟩, ⟨1267650600228229401496703205376, 0, 1267650600228229401496703205376⟩, ⟨1267650600228229401496703205376, 0, 1267650600228229401496703205376⟩⟩
theorem checkedGate0403_join : GateValid checkedGate0403 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0404 : Gate := ⟨⟨1267650600228229401496703205376, 0, 1267650600228229401496703205376⟩, ⟨1, 0, 0⟩, ⟨1267650600228229401496703205377, 0, 1267650600228229401496703205376⟩⟩
theorem checkedGate0404_join : GateValid checkedGate0404 := by
  exact Exists.intro 0 (Exists.intro 1267650600228229401496703205376 (Exists.intro 0 (by decide)))

def checkedGate0405 : Gate := ⟨⟨1267650600228229401496703205377, 0, 1267650600228229401496703205376⟩, ⟨1267650600228229401496703205376, 1267650600228229401496703205376, 0⟩, ⟨2535301200456458802993406410753, 0, 0⟩⟩
theorem checkedGate0405_join : GateValid checkedGate0405 := by
  exact Exists.intro 1267650600228229401496703205376 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGate0406 : Gate := ⟨⟨2535301200456458802993406410753, 0, 0⟩, ⟨0, 0, 0⟩, ⟨2535301200456458802993406410753, 0, 0⟩⟩
theorem checkedGate0406_join : GateValid checkedGate0406 := by
  exact Exists.intro 0 (Exists.intro 0 (Exists.intro 0 (by decide)))

def checkedGateList : List Gate := [checkedGate0000, checkedGate0001, checkedGate0002, checkedGate0003, checkedGate0004, checkedGate0005, checkedGate0006, checkedGate0007, checkedGate0008, checkedGate0009, checkedGate0010, checkedGate0011, checkedGate0012, checkedGate0013, checkedGate0014, checkedGate0015, checkedGate0016, checkedGate0017, checkedGate0018, checkedGate0019, checkedGate0020, checkedGate0021, checkedGate0022, checkedGate0023, checkedGate0024, checkedGate0025, checkedGate0026, checkedGate0027, checkedGate0028, checkedGate0029, checkedGate0030, checkedGate0031, checkedGate0032, checkedGate0033, checkedGate0034, checkedGate0035, checkedGate0036, checkedGate0037, checkedGate0038, checkedGate0039, checkedGate0040, checkedGate0041, checkedGate0042, checkedGate0043, checkedGate0044, checkedGate0045, checkedGate0046, checkedGate0047, checkedGate0048, checkedGate0049, checkedGate0050, checkedGate0051, checkedGate0052, checkedGate0053, checkedGate0054, checkedGate0055, checkedGate0056, checkedGate0057, checkedGate0058, checkedGate0059, checkedGate0060, checkedGate0061, checkedGate0062, checkedGate0063, checkedGate0064, checkedGate0065, checkedGate0066, checkedGate0067, checkedGate0068, checkedGate0069, checkedGate0070, checkedGate0071, checkedGate0072, checkedGate0073, checkedGate0074, checkedGate0075, checkedGate0076, checkedGate0077, checkedGate0078, checkedGate0079, checkedGate0080, checkedGate0081, checkedGate0082, checkedGate0083, checkedGate0084, checkedGate0085, checkedGate0086, checkedGate0087, checkedGate0088, checkedGate0089, checkedGate0090, checkedGate0091, checkedGate0092, checkedGate0093, checkedGate0094, checkedGate0095, checkedGate0096, checkedGate0097, checkedGate0098, checkedGate0099, checkedGate0100, checkedGate0101, checkedGate0102, checkedGate0103, checkedGate0104, checkedGate0105, checkedGate0106, checkedGate0107, checkedGate0108, checkedGate0109, checkedGate0110, checkedGate0111, checkedGate0112, checkedGate0113, checkedGate0114, checkedGate0115, checkedGate0116, checkedGate0117, checkedGate0118, checkedGate0119, checkedGate0120, checkedGate0121, checkedGate0122, checkedGate0123, checkedGate0124, checkedGate0125, checkedGate0126, checkedGate0127, checkedGate0128, checkedGate0129, checkedGate0130, checkedGate0131, checkedGate0132, checkedGate0133, checkedGate0134, checkedGate0135, checkedGate0136, checkedGate0137, checkedGate0138, checkedGate0139, checkedGate0140, checkedGate0141, checkedGate0142, checkedGate0143, checkedGate0144, checkedGate0145, checkedGate0146, checkedGate0147, checkedGate0148, checkedGate0149, checkedGate0150, checkedGate0151, checkedGate0152, checkedGate0153, checkedGate0154, checkedGate0155, checkedGate0156, checkedGate0157, checkedGate0158, checkedGate0159, checkedGate0160, checkedGate0161, checkedGate0162, checkedGate0163, checkedGate0164, checkedGate0165, checkedGate0166, checkedGate0167, checkedGate0168, checkedGate0169, checkedGate0170, checkedGate0171, checkedGate0172, checkedGate0173, checkedGate0174, checkedGate0175, checkedGate0176, checkedGate0177, checkedGate0178, checkedGate0179, checkedGate0180, checkedGate0181, checkedGate0182, checkedGate0183, checkedGate0184, checkedGate0185, checkedGate0186, checkedGate0187, checkedGate0188, checkedGate0189, checkedGate0190, checkedGate0191, checkedGate0192, checkedGate0193, checkedGate0194, checkedGate0195, checkedGate0196, checkedGate0197, checkedGate0198, checkedGate0199, checkedGate0200, checkedGate0201, checkedGate0202, checkedGate0203, checkedGate0204, checkedGate0205, checkedGate0206, checkedGate0207, checkedGate0208, checkedGate0209, checkedGate0210, checkedGate0211, checkedGate0212, checkedGate0213, checkedGate0214, checkedGate0215, checkedGate0216, checkedGate0217, checkedGate0218, checkedGate0219, checkedGate0220, checkedGate0221, checkedGate0222, checkedGate0223, checkedGate0224, checkedGate0225, checkedGate0226, checkedGate0227, checkedGate0228, checkedGate0229, checkedGate0230, checkedGate0231, checkedGate0232, checkedGate0233, checkedGate0234, checkedGate0235, checkedGate0236, checkedGate0237, checkedGate0238, checkedGate0239, checkedGate0240, checkedGate0241, checkedGate0242, checkedGate0243, checkedGate0244, checkedGate0245, checkedGate0246, checkedGate0247, checkedGate0248, checkedGate0249, checkedGate0250, checkedGate0251, checkedGate0252, checkedGate0253, checkedGate0254, checkedGate0255, checkedGate0256, checkedGate0257, checkedGate0258, checkedGate0259, checkedGate0260, checkedGate0261, checkedGate0262, checkedGate0263, checkedGate0264, checkedGate0265, checkedGate0266, checkedGate0267, checkedGate0268, checkedGate0269, checkedGate0270, checkedGate0271, checkedGate0272, checkedGate0273, checkedGate0274, checkedGate0275, checkedGate0276, checkedGate0277, checkedGate0278, checkedGate0279, checkedGate0280, checkedGate0281, checkedGate0282, checkedGate0283, checkedGate0284, checkedGate0285, checkedGate0286, checkedGate0287, checkedGate0288, checkedGate0289, checkedGate0290, checkedGate0291, checkedGate0292, checkedGate0293, checkedGate0294, checkedGate0295, checkedGate0296, checkedGate0297, checkedGate0298, checkedGate0299, checkedGate0300, checkedGate0301, checkedGate0302, checkedGate0303, checkedGate0304, checkedGate0305, checkedGate0306, checkedGate0307, checkedGate0308, checkedGate0309, checkedGate0310, checkedGate0311, checkedGate0312, checkedGate0313, checkedGate0314, checkedGate0315, checkedGate0316, checkedGate0317, checkedGate0318, checkedGate0319, checkedGate0320, checkedGate0321, checkedGate0322, checkedGate0323, checkedGate0324, checkedGate0325, checkedGate0326, checkedGate0327, checkedGate0328, checkedGate0329, checkedGate0330, checkedGate0331, checkedGate0332, checkedGate0333, checkedGate0334, checkedGate0335, checkedGate0336, checkedGate0337, checkedGate0338, checkedGate0339, checkedGate0340, checkedGate0341, checkedGate0342, checkedGate0343, checkedGate0344, checkedGate0345, checkedGate0346, checkedGate0347, checkedGate0348, checkedGate0349, checkedGate0350, checkedGate0351, checkedGate0352, checkedGate0353, checkedGate0354, checkedGate0355, checkedGate0356, checkedGate0357, checkedGate0358, checkedGate0359, checkedGate0360, checkedGate0361, checkedGate0362, checkedGate0363, checkedGate0364, checkedGate0365, checkedGate0366, checkedGate0367, checkedGate0368, checkedGate0369, checkedGate0370, checkedGate0371, checkedGate0372, checkedGate0373, checkedGate0374, checkedGate0375, checkedGate0376, checkedGate0377, checkedGate0378, checkedGate0379, checkedGate0380, checkedGate0381, checkedGate0382, checkedGate0383, checkedGate0384, checkedGate0385, checkedGate0386, checkedGate0387, checkedGate0388, checkedGate0389, checkedGate0390, checkedGate0391, checkedGate0392, checkedGate0393, checkedGate0394, checkedGate0395, checkedGate0396, checkedGate0397, checkedGate0398, checkedGate0399, checkedGate0400, checkedGate0401, checkedGate0402, checkedGate0403, checkedGate0404, checkedGate0405, checkedGate0406]

theorem checked_gate_list_matches_computation : checkedGateList = computedGateList := by decide

theorem checked_gates_valid : GatesValid checkedGateList := by
  exact And.intro checkedGate0000_join (And.intro checkedGate0001_join (And.intro checkedGate0002_join (And.intro checkedGate0003_join (And.intro checkedGate0004_join (And.intro checkedGate0005_join (And.intro checkedGate0006_join (And.intro checkedGate0007_join (And.intro checkedGate0008_join (And.intro checkedGate0009_join (And.intro checkedGate0010_join (And.intro checkedGate0011_join (And.intro checkedGate0012_join (And.intro checkedGate0013_join (And.intro checkedGate0014_join (And.intro checkedGate0015_join (And.intro checkedGate0016_join (And.intro checkedGate0017_join (And.intro checkedGate0018_join (And.intro checkedGate0019_join (And.intro checkedGate0020_join (And.intro checkedGate0021_join (And.intro checkedGate0022_join (And.intro checkedGate0023_join (And.intro checkedGate0024_join (And.intro checkedGate0025_join (And.intro checkedGate0026_join (And.intro checkedGate0027_join (And.intro checkedGate0028_join (And.intro checkedGate0029_join (And.intro checkedGate0030_join (And.intro checkedGate0031_join (And.intro checkedGate0032_join (And.intro checkedGate0033_join (And.intro checkedGate0034_join (And.intro checkedGate0035_join (And.intro checkedGate0036_join (And.intro checkedGate0037_join (And.intro checkedGate0038_join (And.intro checkedGate0039_join (And.intro checkedGate0040_join (And.intro checkedGate0041_join (And.intro checkedGate0042_join (And.intro checkedGate0043_join (And.intro checkedGate0044_join (And.intro checkedGate0045_join (And.intro checkedGate0046_join (And.intro checkedGate0047_join (And.intro checkedGate0048_join (And.intro checkedGate0049_join (And.intro checkedGate0050_join (And.intro checkedGate0051_join (And.intro checkedGate0052_join (And.intro checkedGate0053_join (And.intro checkedGate0054_join (And.intro checkedGate0055_join (And.intro checkedGate0056_join (And.intro checkedGate0057_join (And.intro checkedGate0058_join (And.intro checkedGate0059_join (And.intro checkedGate0060_join (And.intro checkedGate0061_join (And.intro checkedGate0062_join (And.intro checkedGate0063_join (And.intro checkedGate0064_join (And.intro checkedGate0065_join (And.intro checkedGate0066_join (And.intro checkedGate0067_join (And.intro checkedGate0068_join (And.intro checkedGate0069_join (And.intro checkedGate0070_join (And.intro checkedGate0071_join (And.intro checkedGate0072_join (And.intro checkedGate0073_join (And.intro checkedGate0074_join (And.intro checkedGate0075_join (And.intro checkedGate0076_join (And.intro checkedGate0077_join (And.intro checkedGate0078_join (And.intro checkedGate0079_join (And.intro checkedGate0080_join (And.intro checkedGate0081_join (And.intro checkedGate0082_join (And.intro checkedGate0083_join (And.intro checkedGate0084_join (And.intro checkedGate0085_join (And.intro checkedGate0086_join (And.intro checkedGate0087_join (And.intro checkedGate0088_join (And.intro checkedGate0089_join (And.intro checkedGate0090_join (And.intro checkedGate0091_join (And.intro checkedGate0092_join (And.intro checkedGate0093_join (And.intro checkedGate0094_join (And.intro checkedGate0095_join (And.intro checkedGate0096_join (And.intro checkedGate0097_join (And.intro checkedGate0098_join (And.intro checkedGate0099_join (And.intro checkedGate0100_join (And.intro checkedGate0101_join (And.intro checkedGate0102_join (And.intro checkedGate0103_join (And.intro checkedGate0104_join (And.intro checkedGate0105_join (And.intro checkedGate0106_join (And.intro checkedGate0107_join (And.intro checkedGate0108_join (And.intro checkedGate0109_join (And.intro checkedGate0110_join (And.intro checkedGate0111_join (And.intro checkedGate0112_join (And.intro checkedGate0113_join (And.intro checkedGate0114_join (And.intro checkedGate0115_join (And.intro checkedGate0116_join (And.intro checkedGate0117_join (And.intro checkedGate0118_join (And.intro checkedGate0119_join (And.intro checkedGate0120_join (And.intro checkedGate0121_join (And.intro checkedGate0122_join (And.intro checkedGate0123_join (And.intro checkedGate0124_join (And.intro checkedGate0125_join (And.intro checkedGate0126_join (And.intro checkedGate0127_join (And.intro checkedGate0128_join (And.intro checkedGate0129_join (And.intro checkedGate0130_join (And.intro checkedGate0131_join (And.intro checkedGate0132_join (And.intro checkedGate0133_join (And.intro checkedGate0134_join (And.intro checkedGate0135_join (And.intro checkedGate0136_join (And.intro checkedGate0137_join (And.intro checkedGate0138_join (And.intro checkedGate0139_join (And.intro checkedGate0140_join (And.intro checkedGate0141_join (And.intro checkedGate0142_join (And.intro checkedGate0143_join (And.intro checkedGate0144_join (And.intro checkedGate0145_join (And.intro checkedGate0146_join (And.intro checkedGate0147_join (And.intro checkedGate0148_join (And.intro checkedGate0149_join (And.intro checkedGate0150_join (And.intro checkedGate0151_join (And.intro checkedGate0152_join (And.intro checkedGate0153_join (And.intro checkedGate0154_join (And.intro checkedGate0155_join (And.intro checkedGate0156_join (And.intro checkedGate0157_join (And.intro checkedGate0158_join (And.intro checkedGate0159_join (And.intro checkedGate0160_join (And.intro checkedGate0161_join (And.intro checkedGate0162_join (And.intro checkedGate0163_join (And.intro checkedGate0164_join (And.intro checkedGate0165_join (And.intro checkedGate0166_join (And.intro checkedGate0167_join (And.intro checkedGate0168_join (And.intro checkedGate0169_join (And.intro checkedGate0170_join (And.intro checkedGate0171_join (And.intro checkedGate0172_join (And.intro checkedGate0173_join (And.intro checkedGate0174_join (And.intro checkedGate0175_join (And.intro checkedGate0176_join (And.intro checkedGate0177_join (And.intro checkedGate0178_join (And.intro checkedGate0179_join (And.intro checkedGate0180_join (And.intro checkedGate0181_join (And.intro checkedGate0182_join (And.intro checkedGate0183_join (And.intro checkedGate0184_join (And.intro checkedGate0185_join (And.intro checkedGate0186_join (And.intro checkedGate0187_join (And.intro checkedGate0188_join (And.intro checkedGate0189_join (And.intro checkedGate0190_join (And.intro checkedGate0191_join (And.intro checkedGate0192_join (And.intro checkedGate0193_join (And.intro checkedGate0194_join (And.intro checkedGate0195_join (And.intro checkedGate0196_join (And.intro checkedGate0197_join (And.intro checkedGate0198_join (And.intro checkedGate0199_join (And.intro checkedGate0200_join (And.intro checkedGate0201_join (And.intro checkedGate0202_join (And.intro checkedGate0203_join (And.intro checkedGate0204_join (And.intro checkedGate0205_join (And.intro checkedGate0206_join (And.intro checkedGate0207_join (And.intro checkedGate0208_join (And.intro checkedGate0209_join (And.intro checkedGate0210_join (And.intro checkedGate0211_join (And.intro checkedGate0212_join (And.intro checkedGate0213_join (And.intro checkedGate0214_join (And.intro checkedGate0215_join (And.intro checkedGate0216_join (And.intro checkedGate0217_join (And.intro checkedGate0218_join (And.intro checkedGate0219_join (And.intro checkedGate0220_join (And.intro checkedGate0221_join (And.intro checkedGate0222_join (And.intro checkedGate0223_join (And.intro checkedGate0224_join (And.intro checkedGate0225_join (And.intro checkedGate0226_join (And.intro checkedGate0227_join (And.intro checkedGate0228_join (And.intro checkedGate0229_join (And.intro checkedGate0230_join (And.intro checkedGate0231_join (And.intro checkedGate0232_join (And.intro checkedGate0233_join (And.intro checkedGate0234_join (And.intro checkedGate0235_join (And.intro checkedGate0236_join (And.intro checkedGate0237_join (And.intro checkedGate0238_join (And.intro checkedGate0239_join (And.intro checkedGate0240_join (And.intro checkedGate0241_join (And.intro checkedGate0242_join (And.intro checkedGate0243_join (And.intro checkedGate0244_join (And.intro checkedGate0245_join (And.intro checkedGate0246_join (And.intro checkedGate0247_join (And.intro checkedGate0248_join (And.intro checkedGate0249_join (And.intro checkedGate0250_join (And.intro checkedGate0251_join (And.intro checkedGate0252_join (And.intro checkedGate0253_join (And.intro checkedGate0254_join (And.intro checkedGate0255_join (And.intro checkedGate0256_join (And.intro checkedGate0257_join (And.intro checkedGate0258_join (And.intro checkedGate0259_join (And.intro checkedGate0260_join (And.intro checkedGate0261_join (And.intro checkedGate0262_join (And.intro checkedGate0263_join (And.intro checkedGate0264_join (And.intro checkedGate0265_join (And.intro checkedGate0266_join (And.intro checkedGate0267_join (And.intro checkedGate0268_join (And.intro checkedGate0269_join (And.intro checkedGate0270_join (And.intro checkedGate0271_join (And.intro checkedGate0272_join (And.intro checkedGate0273_join (And.intro checkedGate0274_join (And.intro checkedGate0275_join (And.intro checkedGate0276_join (And.intro checkedGate0277_join (And.intro checkedGate0278_join (And.intro checkedGate0279_join (And.intro checkedGate0280_join (And.intro checkedGate0281_join (And.intro checkedGate0282_join (And.intro checkedGate0283_join (And.intro checkedGate0284_join (And.intro checkedGate0285_join (And.intro checkedGate0286_join (And.intro checkedGate0287_join (And.intro checkedGate0288_join (And.intro checkedGate0289_join (And.intro checkedGate0290_join (And.intro checkedGate0291_join (And.intro checkedGate0292_join (And.intro checkedGate0293_join (And.intro checkedGate0294_join (And.intro checkedGate0295_join (And.intro checkedGate0296_join (And.intro checkedGate0297_join (And.intro checkedGate0298_join (And.intro checkedGate0299_join (And.intro checkedGate0300_join (And.intro checkedGate0301_join (And.intro checkedGate0302_join (And.intro checkedGate0303_join (And.intro checkedGate0304_join (And.intro checkedGate0305_join (And.intro checkedGate0306_join (And.intro checkedGate0307_join (And.intro checkedGate0308_join (And.intro checkedGate0309_join (And.intro checkedGate0310_join (And.intro checkedGate0311_join (And.intro checkedGate0312_join (And.intro checkedGate0313_join (And.intro checkedGate0314_join (And.intro checkedGate0315_join (And.intro checkedGate0316_join (And.intro checkedGate0317_join (And.intro checkedGate0318_join (And.intro checkedGate0319_join (And.intro checkedGate0320_join (And.intro checkedGate0321_join (And.intro checkedGate0322_join (And.intro checkedGate0323_join (And.intro checkedGate0324_join (And.intro checkedGate0325_join (And.intro checkedGate0326_join (And.intro checkedGate0327_join (And.intro checkedGate0328_join (And.intro checkedGate0329_join (And.intro checkedGate0330_join (And.intro checkedGate0331_join (And.intro checkedGate0332_join (And.intro checkedGate0333_join (And.intro checkedGate0334_join (And.intro checkedGate0335_join (And.intro checkedGate0336_join (And.intro checkedGate0337_join (And.intro checkedGate0338_join (And.intro checkedGate0339_join (And.intro checkedGate0340_join (And.intro checkedGate0341_join (And.intro checkedGate0342_join (And.intro checkedGate0343_join (And.intro checkedGate0344_join (And.intro checkedGate0345_join (And.intro checkedGate0346_join (And.intro checkedGate0347_join (And.intro checkedGate0348_join (And.intro checkedGate0349_join (And.intro checkedGate0350_join (And.intro checkedGate0351_join (And.intro checkedGate0352_join (And.intro checkedGate0353_join (And.intro checkedGate0354_join (And.intro checkedGate0355_join (And.intro checkedGate0356_join (And.intro checkedGate0357_join (And.intro checkedGate0358_join (And.intro checkedGate0359_join (And.intro checkedGate0360_join (And.intro checkedGate0361_join (And.intro checkedGate0362_join (And.intro checkedGate0363_join (And.intro checkedGate0364_join (And.intro checkedGate0365_join (And.intro checkedGate0366_join (And.intro checkedGate0367_join (And.intro checkedGate0368_join (And.intro checkedGate0369_join (And.intro checkedGate0370_join (And.intro checkedGate0371_join (And.intro checkedGate0372_join (And.intro checkedGate0373_join (And.intro checkedGate0374_join (And.intro checkedGate0375_join (And.intro checkedGate0376_join (And.intro checkedGate0377_join (And.intro checkedGate0378_join (And.intro checkedGate0379_join (And.intro checkedGate0380_join (And.intro checkedGate0381_join (And.intro checkedGate0382_join (And.intro checkedGate0383_join (And.intro checkedGate0384_join (And.intro checkedGate0385_join (And.intro checkedGate0386_join (And.intro checkedGate0387_join (And.intro checkedGate0388_join (And.intro checkedGate0389_join (And.intro checkedGate0390_join (And.intro checkedGate0391_join (And.intro checkedGate0392_join (And.intro checkedGate0393_join (And.intro checkedGate0394_join (And.intro checkedGate0395_join (And.intro checkedGate0396_join (And.intro checkedGate0397_join (And.intro checkedGate0398_join (And.intro checkedGate0399_join (And.intro checkedGate0400_join (And.intro checkedGate0401_join (And.intro checkedGate0402_join (And.intro checkedGate0403_join (And.intro checkedGate0404_join (And.intro checkedGate0405_join (And.intro checkedGate0406_join (True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem computed_gates_valid : GatesValid computedGateList := by
  rw [← checked_gate_list_matches_computation]
  exact checked_gates_valid

end MAISO11.SummaryFiniteCheck
