import Lean
import LeanGpu.Linear

/-!
# The `farkas` tactic

`farkas` closes a goal whose linear hypotheses over `Int` are contradictory
(or proves a linear goal by contradiction). It reads hypotheses
`a ≤ b`, `a < b`, `a ≥ b`, `a > b`, `a = b` and their negations, where both sides
are built from `+`, `-`, numerals and multiplication by numerals. Any other
subterm is treated as an opaque atom.

Certificates come from the solver (`gpu/build/farkas`) and are cached in
`.farkas/cache.txt`, keyed by the problem. A cache hit needs no solver, so
committing the cache lets anyone rebuild. The certificate is never trusted:
the proof goes through `farkas_sound`, and the kernel re-checks it.

* default: on a cache miss, run the solver for this goal and cache the result.
* `set_option farkas.batch true`: on a cache miss, queue the goal in
  `.farkas/pending.txt` and close it with `sorry`. `scripts/farkas-batch.sh` then
  solves every queued goal in one solver run, and the next build uses the cache.
-/

register_option farkas.batch : Bool := {
  defValue := false
  descr := "farkas: on a cache miss, queue the goal for scripts/farkas-batch.sh and admit it"
}

register_option farkas.solver : String := {
  defValue := "gpu/build/farkas"
  descr := "farkas: path to the certificate solver"
}

namespace LeanGpu.FarkasTactic

open Lean Meta Elab Tactic

def farkasDir : System.FilePath := ".farkas"
def cacheFile : System.FilePath := farkasDir / "cache.txt"
def pendingFile : System.FilePath := farkasDir / "pending.txt"

def lexprToExpr : LExpr → Expr
  | .atom i => mkApp (mkConst ``LExpr.atom) (toExpr i)
  | .const c => mkApp (mkConst ``LExpr.const) (toExpr c)
  | .add a b => mkApp2 (mkConst ``LExpr.add) (lexprToExpr a) (lexprToExpr b)
  | .sub a b => mkApp2 (mkConst ``LExpr.sub) (lexprToExpr a) (lexprToExpr b)
  | .neg a => mkApp (mkConst ``LExpr.neg) (lexprToExpr a)
  | .mulL c a => mkApp2 (mkConst ``LExpr.mulL) (toExpr c) (lexprToExpr a)
  | .mulR a c => mkApp2 (mkConst ``LExpr.mulR) (lexprToExpr a) (toExpr c)

abbrev ReifyM := StateT (Array Expr) MetaM

def atom (e : Expr) : ReifyM LExpr := do
  let atoms ← get
  for h : i in [:atoms.size] do
    if ← isDefEq atoms[i] e then return .atom i
  set (atoms.push e)
  return .atom atoms.size

/-- Read an `Int` term as a linear expression. `eval` of the result unfolds to `e`. -/
partial def reify (e : Expr) : ReifyM LExpr := do
  if let some c ← getIntValue? e then return .const c
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => return .add (← reify a) (← reify b)
  | HSub.hSub _ _ _ _ a b => return .sub (← reify a) (← reify b)
  | Neg.neg _ _ a => return .neg (← reify a)
  | HMul.hMul _ _ _ _ a b =>
    if let some c ← getIntValue? a then return .mulL c (← reify b)
    if let some c ← getIntValue? b then return .mulR (← reify a) c
    atom e
  | _ => atom e

/-- `lhs ≤ rhs`, with a proof of `lhs.eval ρ ≤ rhs.eval ρ` (up to unfolding `eval`). -/
structure Fact where
  lhs : LExpr
  rhs : LExpr
  proof : Expr

def isInt (α : Expr) : MetaM Bool := isDefEq α (mkConst ``Int)

/-- `a < b` as `a + 1 ≤ b`. -/
def ltFact (a b h : Expr) : ReifyM Fact := do
  return ⟨.add (← reify a) (.const 1), ← reify b, ← mkAppM ``Int.add_one_le_of_lt #[h]⟩

/-- The linear facts a hypothesis `h : t` gives. -/
def factsOf (t h : Expr) : ReifyM (List Fact) := do
  match_expr ← whnfR t with
  | LE.le α _ a b =>
    if ← isInt α then return [⟨← reify a, ← reify b, h⟩] else return []
  | LT.lt α _ a b =>
    if ← isInt α then return [← ltFact a b h] else return []
  | Eq α a b =>
    if ← isInt α then
      return [⟨← reify a, ← reify b, ← mkAppM ``Int.le_of_eq #[h]⟩,
              ⟨← reify b, ← reify a, ← mkAppM ``Int.le_of_eq #[← mkEqSymm h]⟩]
    else return []
  | Not p =>
    match_expr ← whnfR p with
    | LE.le α _ a b =>
      if ← isInt α then
        return [← ltFact b a (← mkAppM ``Iff.mp #[← mkAppOptM ``Int.not_le #[a, b], h])]
      else return []
    | LT.lt α _ a b =>
      if ← isInt α then
        return [⟨← reify b, ← reify a, ← mkAppM ``Iff.mp #[← mkAppOptM ``Int.not_lt #[a, b], h]⟩]
      else return []
    | _ => return []
  | _ => return []

/-- Cache key: `m n|row;row;…` with each row `a₁ … aₙ b`. -/
def problemKey (n : Nat) (rows : List Row) : String :=
  let row (r : Row) := " ".intercalate ((r.coeffs ++ [r.bound]).map toString)
  s!"{rows.length} {n}|" ++ ";".intercalate (rows.map row)

def parseCert (s : String) : Option (List Nat) :=
  (s.splitOn " ").filter (· ≠ "") |>.mapM String.toNat?

def cacheLookup (key : String) : IO (Option (List Nat)) := do
  unless ← cacheFile.pathExists do return none
  for line in (← IO.FS.readFile cacheFile).splitOn "\n" do
    if let [k, cert] := line.splitOn "\t" then
      if k == key then return parseCert cert
  return none

def appendLine (file : System.FilePath) (line : String) : IO Unit := do
  IO.FS.createDirAll farkasDir
  let h ← IO.FS.Handle.mk file .append
  h.putStrLn line

/-- Run the solver on one problem. -/
def solve (solver : String) (key : String) (n : Nat) (rows : List Row) : IO (Option (List Nat)) := do
  IO.FS.createDirAll farkasDir
  let base := farkasDir / s!"query-{hash key}"
  let input := base.addExtension "txt"
  let output := base.addExtension "certs"
  let row (r : Row) := " ".intercalate ((r.coeffs ++ [r.bound]).map toString)
  IO.FS.writeFile input (s!"goal {rows.length} {n}\n" ++ "\n".intercalate (rows.map row) ++ "\n")
  let res ← IO.Process.output { cmd := solver, args := #["--certs", input.toString, output.toString] }
  if res.exitCode != 0 then
    throw <| IO.userError s!"farkas: solver `{solver}` failed:\n{res.stderr}"
  let out ← IO.FS.readFile output
  IO.FS.removeFile input
  IO.FS.removeFile output
  match ((out.splitOn "\n").headD "").splitOn " " with
  | "goal" :: "-" :: _ => return none
  | "goal" :: cert => return parseCert (" ".intercalate cert)
  | _ => throw <| IO.userError s!"farkas: unexpected solver output: {out}"

def farkas (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let some g ← g.falseOrByContra | return []
  g.withContext do
  let mut facts : Array Fact := #[]
  let mut atoms : Array Expr := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let (fs, atoms') ← (factsOf (← instantiateMVars decl.type) decl.toExpr).run atoms
    facts := facts ++ fs
    atoms := atoms'
  if facts.isEmpty then throwError "farkas: no linear hypotheses over Int"
  let n := atoms.size
  let rows := facts.toList.map fun f => leRow n f.lhs f.rhs
  let key := problemKey n rows

  let cert ← match ← cacheLookup key with
    | some cert => pure cert
    | none =>
      let opts ← getOptions
      if farkas.batch.get opts then
        appendLine pendingFile key
        logWarning "farkas: queued for scripts/farkas-batch.sh (goal admitted)"
        g.admit
        return []
      match ← solve (farkas.solver.get opts) key n rows with
      | some cert => appendLine cacheFile s!"{key}\t{" ".intercalate (cert.map toString)}"; pure cert
      | none => throwError "farkas: no certificate found; the hypotheses may be satisfiable"
  unless check n rows cert do
    throwError "farkas: cached certificate does not check (stale .farkas/cache.txt?)"

  let nE := toExpr n
  let ρE ← mkListLit (mkConst ``Int) atoms.toList
  let hρ ← mkEqRefl nE
  let mut holds ← mkAppM ``holds_nil #[ρE]
  let mut rowEs : List Expr := []
  for f in facts.reverse do
    let lhsE := lexprToExpr f.lhs
    let rhsE := lexprToExpr f.rhs
    let h ← mkAppM ``leRow_holds #[nE, ρE, hρ, lhsE, rhsE, f.proof]
    holds ← mkAppM ``holds_cons #[h, holds]
    rowEs := mkApp3 (mkConst ``leRow) nE lhsE rhsE :: rowEs
  let rowsE ← mkListLit (mkConst ``Row) rowEs
  let lamE ← mkListLit (mkConst ``Nat) (cert.map toExpr)
  let checkE := mkApp3 (mkConst ``check) nE rowsE lamE
  let hcheck ← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) (← mkEq checkE (mkConst ``Bool.true))
  g.assign (mkAppN (mkConst ``farkas_sound) #[nE, rowsE, lamE, hcheck, ρE, holds])
  return []

/-- Close a goal from contradictory linear hypotheses over `Int`, with a certificate
from the (GPU) solver that the kernel re-checks. See the module docs. -/
elab "farkas" : tactic => liftMetaTactic farkas

end LeanGpu.FarkasTactic
