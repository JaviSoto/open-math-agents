import RankTwoInteriorCover245212

/-! Generate source with short, independently checkable subtrees. Numeric
choices and the emitted split arithmetic are all rechecked by Lean. Run
with --run FILE OUTPUT MODULE m kl kh maxNodes maxPositions. -/
open OMA.RankTwoInteriorBox245212 OMA.RankTwoInteriorWalk245212 OMA.RankTwoInteriorCover245212

private inductive Plan where
  | leaf (t : Cell) (nodes positions : ℕ) (script : String)
  | pair (t : Cell) (left right : Plan) (nodes positions : ℕ)

private def Plan.cost : Plan → ℕ × ℕ
  | .leaf _ n p _ | .pair _ _ _ n p => (n,p)

private def plan (maxNodes maxPositions : ℕ) (fuel : ℕ) (raw : Cell) : Plan :=
  let t := trim raw
  if t.ph<t.pl then .leaf raw 1 0 "e" else
  if OMA.RankTwoInteriorBox245212.veto t then .leaf raw 1 0 "p" else
  if OMA.OddBox245212.veto t.kl t.kh t.bl t.bh t.cl t.ch t.pl t.ph then .leaf raw 1 0 "g" else
  let atLeaf := Plan.leaf raw 1 (spend t) "a"
  match fuel with
  | 0 => atLeaf
  | fuel+1 =>
    if spend t≤160 then atLeaf else
    let (l,r) := halves t
    let a := plan maxNodes maxPositions fuel l
    let b := plan maxNodes maxPositions fuel r
    let n := 1+a.cost.1+b.cost.1
    let p := a.cost.2+b.cost.2
    match a,b with
    | .leaf _ _ _ l,.leaf _ _ _ r =>
      if n ≤ maxNodes && p ≤ maxPositions then .leaf raw n p s!"(s {l} {r})" else .pair raw a b n p
    | _,_ => .pair raw a b n p

private def coords (t : Cell) : String :=
  s!"⟨{t.kl},{t.kh},{t.bl},{t.bh},{t.cl},{t.ch},{t.pl},{t.ph}⟩"

private def emit (out : IO.FS.Handle) (tree : Plan) (i : ℕ) : IO ℕ := do
  match tree with
  | .leaf t _ _ script =>
    out.putStrLn s!"private theorem n{i} : Closed {coords t} := of_script {script} _ (by decide +kernel)"
    return i
  | .pair t a b _ _ =>
    let l ← emit out a i
    let r ← emit out b (l+1)
    let j := r+1
    out.putStrLn s!"private theorem n{j} : Closed {coords t} := join _ n{l} n{r} (by decide +kernel)"
    return j

def main (args : List String) : IO UInt32 := do
  let [file,name,m,kl,kh,nodes,positions] := args | throw <| IO.userError "OUTPUT MODULE m kl kh maxNodes maxPositions"
  let some [m,kl,kh,nodes,positions] := [m,kl,kh,nodes,positions].mapM String.toNat?
    | throw <| IO.userError "integer arguments required"
  if !(6 ≤ m && m ≤ 32 && 6 ≤ kl && kl ≤ kh && kh ≤ 1250 && 0 < nodes && 0 < positions &&
      name.toList.all Char.isAlphanum) then throw <| IO.userError "invalid interval or module"
  let h ← IO.FS.Handle.mk file .write
  h.putStrLn "import RankTwoInteriorCover245212\n/-! Checked rank-two finite arithmetic. -/"
  h.putStrLn s!"namespace OMA.{name}\nopen OMA.RankTwoInteriorCover245212 OMA.RankTwoInteriorWalk245212"
  h.putStrLn "private abbrev e := Script.leaf .empty\nprivate abbrev p := Script.leaf .pole\nprivate abbrev g := Script.leaf .exterior\nprivate abbrev a := Script.leaf .arithmetic\nprivate abbrev s := Script.fork"
  h.putStrLn "set_option maxHeartbeats 0\nset_option maxRecDepth 20000"
  let left := plan nodes positions 40 (root m kl kh false)
  let last ← emit h left 0
  h.putStrLn s!"theorem normal : Closed (root {m} {kl} {kh} false) := n{last}"
  let right := plan nodes positions 40 (root m kl kh true)
  let final ← emit h right (last+1)
  h.putStrLn s!"theorem reverse : Closed (root {m} {kl} {kh} true) := n{final}"
  h.putStrLn s!"#print axioms normal\n#print axioms reverse\nend OMA.{name}"
  IO.println s!"{name}: {final+1} declarations; nodes={left.cost.1+right.cost.1}, integer positions={left.cost.2+right.cost.2}"
  return 0
