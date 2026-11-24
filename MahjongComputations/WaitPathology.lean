module

public import Mahjong.WaitCompletionFinder
public import Mahjong.WaitDecompositionCode
public import MahjongComputations.WaitCoreReduction

@[expose] public section

open MahjongDomain (Tile)

namespace MahjongComputations

open WaitDecompositionCode

def waitPathologyWitnessesCached (tiles : List Tile) (completions : List WaitCompletion)
    (cache : WaitCoreCache) : List WaitPathologyWitness × WaitCoreCache :=
  let computation : StateM WaitCoreCache (List WaitPathologyWitness) :=
    waitPathologyWitnessesWith tiles completions fun remaining =>
      get >>= fun cache =>
      let (cores, cache) := Internal.cachedWaitCores remaining cache
      set cache *> pure cores
  computation.run cache

structure WaitPathologyGroup where
  codes : List Nat
  reducible : Bool
  count : Nat
  representativeTiles : List Tile
  representativeWaits : List Tile
  witness : WaitPathologyWitness
deriving BEq, DecidableEq, Repr

def mergeWaitPathologyGroups (groups additions : List WaitPathologyGroup) :
    List WaitPathologyGroup :=
  additions.foldl (fun merged addition =>
    let rec add : List WaitPathologyGroup → List WaitPathologyGroup
      | [] => [addition]
      | group :: rest =>
        if group.codes == addition.codes && group.reducible == addition.reducible &&
            group.witness.pathology == addition.witness.pathology then
          { group with count := group.count + addition.count } :: rest
        else group :: add rest
    add merged) groups

def addWaitPathologyGroups (tiles : List Tile) (completions : List WaitCompletion)
    (reducible : Bool) (witnesses : List WaitPathologyWitness)
    (groups : List WaitPathologyGroup) : List WaitPathologyGroup :=
  if witnesses.isEmpty then groups else
  let codes := waitDecompositionCodes completions
  let waits := (completions.map (·.wait)).eraseDups
  mergeWaitPathologyGroups groups <| witnesses.map fun witness => {
    codes, reducible, count := 1, representativeTiles := tiles,
    representativeWaits := waits, witness
  }

end MahjongComputations