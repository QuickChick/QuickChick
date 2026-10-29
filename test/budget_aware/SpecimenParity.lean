-- Golden scores from Specimen 121cf23435a17d93f1dde283daa62d2899628a8b.
-- Run with `lake env lean` from that checkout.
import Specimen.Scoring
open Lean Schedules Scoring

inductive Pinned : Nat → Prop where
  | zero : Pinned 0
  | one : Pinned 1

inductive Unpinned : Nat → Prop where
  | zero : Unpinned 0
  | any (n : Nat) : Unpinned n

private def showScore (label : String) (score : BudgetAwareScore) : MetaM Unit := do
  IO.println s!"{label}: {score.selectivity},{score.density.toNat},{score.fabrication},{score.locality.toNat},{score.inputCheckDeps},{score.varDeps}"

#eval show MetaM Unit from do
  IO.println s!"pinned-positions: {← finitePinnedArgPositions ``Pinned}"
  IO.println s!"unpinned-positions: {← finitePinnedArgPositions ``Unpinned}"
  let genKey : SpecKey := { inductiveName := `Root, outputIndices := [0], deriveSort := .Generator }
  let checkKey := { genKey with deriveSort := .Checker }
  let depKey : SpecKey := { inductiveName := `Dep, outputIndices := [0], deriveSort := .Checker }
  let enumKey := { depKey with deriveSort := .Enumerator }
  let depScore : BudgetAwareScore := { density := .Checking }
  let enumScore : BudgetAwareScore := { density := .Partial, fabrication := 5 }
  let mkDep (key : SpecKey) (score : BudgetAwareScore) : MemoEntry :=
    .done { key, argNames := [], recFnName := `rec, baseSchedules := [],
            recSchedules := [], score := Score.wrap score }
  let memo : Std.HashMap SpecKey MemoEntry := (({} : Std.HashMap SpecKey MemoEntry).insert depKey (mkDep depKey depScore))
    |>.insert enumKey (mkDep enumKey enumScore)
  let emptyMemo : Std.HashMap SpecKey MemoEntry := {}
  let mixed := Source.NonRec (`Rel, [.Unknown `x, .Unknown `y, .Unknown `y])
  showScore "mixed-check" (← budgetAwareStepScorer genKey emptyMemo
    (Std.HashSet.ofList [`x]) (.Check mixed true))
  showScore "type-parameter" (← budgetAwareStepScorer genKey emptyMemo
    (Std.HashSet.ofList [`T])
    (.Check (.NonRec (`Rel, [.Unknown `T, .Unknown `x])) true))
  showScore "checker-arbitrary" (← budgetAwareStepScorer checkKey emptyMemo
    {} (.Unconstrained `y (.NonRec (`Nat, [])) .Enumerator))
  showScore "checker-dependency" (← budgetAwareStepScorer checkKey memo
    {} (.SuchThat [(`y, none)] (.NonRec (`Dep, [.Unknown `y])) .Enumerator))
  showScore "generator-dependency" (← budgetAwareStepScorer genKey memo
    {} (.SuchThat [(`y, none)] (.NonRec (`Dep, [.Unknown `y])) .Generator))
  showScore "recursive" (← budgetAwareStepScorer genKey emptyMemo
    {} (.SuchThat [(`y, none)] (.Rec `rec [.Unknown `y]) .Generator))
  showScore "same-relation" (← budgetAwareStepScorer genKey emptyMemo
    {} (.SuchThat [(`y, none)] (.NonRec (`Root, [.Unknown `y])) .Generator))
  let loose : List ScheduleStep := [
    .Unconstrained `v (.NonRec (`Nat, [])) .Generator,
    .Check (.NonRec (``Pinned, [.Unknown `v])) true]
  let looseScore := Score.unwrap BudgetAwareScore (←
    budgetAwareWholeScheduleScorer genKey emptyMemo {} loose)
  showScore "loose-pinned" looseScore
  let twice := loose ++ [.Check (.NonRec (``Pinned, [.Unknown `v])) true]
  showScore "loose-two-pins" (Score.unwrap BudgetAwareScore (←
    budgetAwareWholeScheduleScorer genKey emptyMemo {} twice))
  let finite : List ScheduleStep := [
    .SuchThat [(`v, none)] (.NonRec (``Pinned, [.Unknown `v])) .Generator]
  let finiteScore := Score.unwrap BudgetAwareScore (←
    budgetAwareWholeScheduleScorer genKey emptyMemo {} finite)
  showScore "finite-producer" finiteScore
  let bestLeaf := budgetAwareLeafAggregator [(`loose, looseScore), (`finite, finiteScore)]
  showScore "best-leaf" bestLeaf
  let uncovered := budgetAwareLeafAggregator []
  showScore "uncovered" uncovered
  showScore "inductive" (budgetAwareInductiveAggregator [bestLeaf, uncovered])
