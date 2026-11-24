module

public import Mahjong.WaitCompletionFinder
public import Mahjong.WaitDecompositionCode

@[expose] public section

open MahjongDomain (Tile)

namespace MahjongComputations

open WaitDecompositionCode

/-- 完成情報群に現れる待ち牌を、初出順で重複なく取り出す。 -/
def waitsFromCompletions (completions : List WaitCompletion) : List Tile :=
  (completions.map fun completion => completion.wait).eraseDups

/-- 同じ待ち分解コード列を持つ牌姿の件数と代表例。 -/
structure WaitDecompositionCodeGroup where
  codes : List Nat
  count : Nat
  representativeTiles : List Tile
  representativeWaits : List Tile
deriving BEq, DecidableEq, Repr

/-- 待ち分解コード列が一致するグループへ牌姿を1件加える。 -/
def addWaitDecompositionCodeGroup
    (codes : List Nat) (tiles waits : List Tile) :
    List WaitDecompositionCodeGroup → List WaitDecompositionCodeGroup
  | [] => [{ codes, count := 1, representativeTiles := tiles, representativeWaits := waits }]
  | group :: rest =>
      if group.codes == codes then
        { group with count := group.count + 1 } :: rest
      else
        group :: addWaitDecompositionCodeGroup codes tiles waits rest

/-- 各値を待ち分解コード列でまとめ、件数と最初の代表例を保持する。 -/
def groupByWaitDecompositionCodes {α : Type}
    (codes : α → List Nat) (tiles waits : α → List Tile) (values : List α) :
    List WaitDecompositionCodeGroup :=
  values.foldl
    (fun groups value => addWaitDecompositionCodeGroup
      (codes value) (tiles value) (waits value) groups)
    []

/-- Irreducible hands grouped by both their decomposition codes and component relations. -/
structure WaitPathologyProfileRepresentative where
  waitSuppression : Bool
  redundantAmbiguity : Bool
  tiles : List Tile
  waits : List Tile
deriving BEq, DecidableEq, Repr

structure WaitDecompositionRelationGroup where
  codes : List Nat
  relationKey : List Nat
  count : Nat
  waitSuppressionCount : Nat := 0
  redundantAmbiguityCount : Nat := 0
  bothPathologiesCount : Nat := 0
  representativeTiles : List Tile
  representativeWaits : List Tile
  relationDescription : String
  pathologyProfileRepresentatives : List WaitPathologyProfileRepresentative := []
deriving BEq, DecidableEq, Repr

def Internal.pathologyProfileRepresentative (tiles waits : List Tile)
    (witnesses : List WaitPathologyWitness) : WaitPathologyProfileRepresentative :=
  { waitSuppression := witnesses.any fun witness =>
      witness.pathology == .waitSuppression
    redundantAmbiguity := witnesses.any fun witness =>
      witness.pathology == .redundantAmbiguity
    tiles
    waits }

def Internal.addPathologyProfileRepresentative
    (representative : WaitPathologyProfileRepresentative) :
    List WaitPathologyProfileRepresentative → List WaitPathologyProfileRepresentative
  | [] => [representative]
  | current :: rest =>
      if current.waitSuppression == representative.waitSuppression &&
          current.redundantAmbiguity == representative.redundantAmbiguity then
        current :: rest
      else
        current :: addPathologyProfileRepresentative representative rest

def Internal.mergePathologyProfileRepresentatives
    (representatives additions : List WaitPathologyProfileRepresentative) :
    List WaitPathologyProfileRepresentative :=
  additions.foldl
    (fun merged addition => addPathologyProfileRepresentative addition merged)
    representatives

def Internal.componentRelationKey (relation : ComponentRelation) : Nat :=
  let tileRelationKey := match relation.tileRelation with
    | .overlapping => 0
    | .disjoint => 1
    | .invalidComponents => 2
  (WaitComponentKind.all.idxOf relation.firstKind * WaitComponentKind.count +
      WaitComponentKind.all.idxOf relation.secondKind) * 3 + tileRelationKey

/-- Stable key for a complete wait-decomposition relation classification. -/
def waitDecompositionRelationKey
    (classification : WaitDecompositionRelationClassification) : List Nat :=
  [classification.signatures.length] ++
    classification.signatures.flatMap fun signature =>
      [signature.code, signature.relations.length] ++
        signature.relations.map Internal.componentRelationKey

def Internal.componentKindName : WaitComponentKind → String
  | .tanki => "tanki"
  | .toitsu => "toitsu"
  | .ryanmen => "ryanmen"
  | .kanchan => "kanchan"
  | .penchan => "penchan"
  | .shuntsu => "shuntsu"
  | .koutsu => "koutsu"

/-- Human-readable per-code component relations, including whether tiles are disjoint. -/
def waitDecompositionRelationDescription
    (classification : WaitDecompositionRelationClassification) : String :=
  String.intercalate " | " <| classification.signatures.map fun signature =>
    s!"{signature.code}: " ++ String.intercalate ", " (signature.relations.map fun relation =>
      let tileRelation := match relation.tileRelation with
        | .overlapping => "overlapping"
        | .disjoint => "disjoint"
        | .invalidComponents => "invalid"
      s!"{Internal.componentKindName relation.firstKind}-{Internal.componentKindName relation.secondKind}={tileRelation}")

/-- Whether a classification contains at least one disjoint component relation. -/
def hasDisjointComponentRelation
    (classification : WaitDecompositionRelationClassification) : Bool :=
  classification.signatures.any fun signature =>
    signature.relations.any fun relation => relation.tileRelation == .disjoint

/-- Add one hand to the group with matching codes and component-relation key. -/
def addWaitDecompositionRelationGroup (codes relationKey : List Nat)
    (tiles waits : List Tile) (description : String)
    (pathologyWitnesses : List WaitPathologyWitness) :
    List WaitDecompositionRelationGroup → List WaitDecompositionRelationGroup
  | groups =>
    let hasSuppression := pathologyWitnesses.any fun witness =>
      witness.pathology == .waitSuppression
    let hasAmbiguity := pathologyWitnesses.any fun witness =>
      witness.pathology == .redundantAmbiguity
    let profileRepresentative :=
      Internal.pathologyProfileRepresentative tiles waits pathologyWitnesses
    let rec add : List WaitDecompositionRelationGroup → List WaitDecompositionRelationGroup
      | [] => [{
          codes, relationKey, count := 1,
          waitSuppressionCount := if hasSuppression then 1 else 0,
          redundantAmbiguityCount := if hasAmbiguity then 1 else 0,
          bothPathologiesCount := if hasSuppression && hasAmbiguity then 1 else 0,
          representativeTiles := tiles, representativeWaits := waits,
          relationDescription := description,
          pathologyProfileRepresentatives := [profileRepresentative]
        }]
      | group :: rest =>
          if group.codes == codes && group.relationKey == relationKey then
            { group with
              count := group.count + 1
              waitSuppressionCount :=
                group.waitSuppressionCount + if hasSuppression then 1 else 0
              redundantAmbiguityCount :=
                group.redundantAmbiguityCount + if hasAmbiguity then 1 else 0
              bothPathologiesCount :=
                group.bothPathologiesCount + if hasSuppression && hasAmbiguity then 1 else 0
              pathologyProfileRepresentatives :=
                Internal.addPathologyProfileRepresentative profileRepresentative
                  group.pathologyProfileRepresentatives
            } :: rest
          else
            group :: add rest
    add groups

/-- Merge relation groups while retaining the first representative of each group. -/
def mergeWaitDecompositionRelationGroups
    (groups additions : List WaitDecompositionRelationGroup) :
    List WaitDecompositionRelationGroup :=
  additions.foldl (fun merged addition =>
    let rec add : List WaitDecompositionRelationGroup → List WaitDecompositionRelationGroup
      | [] => [addition]
      | group :: rest =>
          if group.codes == addition.codes && group.relationKey == addition.relationKey then
            { group with
              count := group.count + addition.count
              waitSuppressionCount :=
                group.waitSuppressionCount + addition.waitSuppressionCount
              redundantAmbiguityCount :=
                group.redundantAmbiguityCount + addition.redundantAmbiguityCount
              bothPathologiesCount :=
                group.bothPathologiesCount + addition.bothPathologiesCount
              pathologyProfileRepresentatives :=
                Internal.mergePathologyProfileRepresentatives group.pathologyProfileRepresentatives
                  addition.pathologyProfileRepresentatives
            } :: rest
          else
            group :: add rest
    add merged) groups

end MahjongComputations