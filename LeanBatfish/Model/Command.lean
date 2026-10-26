import LeanBatfish.Decode.Snapshot
import LeanBatfish.Model.Network
import LeanBatfish.Model.ToExpr

/-!
# The `batfish_snapshot` command

    batfish_snapshot Networks.Example from "export"

reads the snapshot that `tools/export.py` exported to that directory when the file is
elaborated, and defines

* `Networks.Example.snapshot`: the snapshot, as an ordinary Lean term;
* `Networks.Example.network`: its network, a routing system with a data plane
  (`LeanBatfish.Model.Network`), modeling every device;
* `Networks.Example.converged`: the state the network converges to from empty tables when
  nothing is announced from outside, by synchronous iteration.

A relative directory is relative to the folder of the file containing the command, so a
network's `Model.lean` reads the export next to it. Rebuilding after a new export picks up
the new snapshot.
-/

namespace LeanBatfish.Model

open Lean Elab Command

syntax (name := batfishSnapshot) "batfish_snapshot " ident " from " str : command

@[command_elab batfishSnapshot]
def elabBatfishSnapshot : CommandElab := fun stx => do
  let ns := stx[1].getId
  let some given := stx[3].isStrLit? | throwError "expected a directory"
  let given : System.FilePath := given
  let here := (System.FilePath.mk (← getFileName)).parent.getD "."
  let dir := if given.isAbsolute then given else here / given
  let snapshot ← match ← liftIO (Decode.snapshot dir) with
    | .ok s => pure s
    | .error e => throwError "cannot read the snapshot in {dir}: {toString e}"
  if let .error e := Network.build snapshot then
    throwError "cannot build the network of the snapshot in {dir}: {e}"
  let name := ns ++ `snapshot
  liftCoreM <| addAndCompile <| .defnDecl {
    name, levelParams := [], type := mkConst ``Snapshot, value := toExpr snapshot
    hints := .opaque, safety := .safe }
  addDocStringCore name s!"The snapshot exported in `{dir}`."
  let snap := mkIdent name
  let net := mkIdent (ns ++ `network)
  let conv := mkIdent (ns ++ `converged)
  elabCommand (← `(
    /-- The network of the snapshot, modeling every device. -/
    def $net : LeanBatfish.Model.Network := LeanBatfish.Model.Network.ofSnapshot $snap))
  elabCommand (← `(
    /-- The state the network reaches from empty tables, with no announcements from
    outside, by synchronous iteration. -/
    def $conv : Fin ($net).size → LeanBatfish.Model.RouterState :=
      ($net).ofArray (($net).converge ($net).quiet)))

end LeanBatfish.Model
