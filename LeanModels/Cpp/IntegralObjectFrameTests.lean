import LeanModels.Cpp.IntegralObjectFrame

namespace LeanModels.Cpp.IntegralObjectFrameTests

open LeanModels.Cpp
open IntegralObjectFrame

private def intType : CppTypeEvidence := .builtin .int
private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩
private def handle (value : String) : FrontendHandle := {value}

private def opened : Except FrameError IntegralObjectFrame := do
  let frame ← IntegralObjectFrame.empty .lp64
  let entered := frame.enterScope
  entered.result.map (fun _ => entered.frame)

private def okValue (expected : IntegralValue) (result : FrameOutcome IntegralValue) : Bool :=
  match result.result with
  | .ok value => value == expected
  | .error _ => false

private def okUnit (result : FrameOutcome Unit) : Bool :=
  match result.result with
  | .ok _ => true
  | .error _ => false

private def objectPhase? (frame : IntegralObjectFrame) (object : ObjectId) : Option ObjectPhase :=
  frame.store.objects.object? object |>.map (·.phase)

private def parameterRead : Bool :=
  match opened with
  | .ok frame =>
      let bound := frame.declareParameter (handle "0x1") intType (signed 7)
      match bound.result with
      | .ok _ => okValue (signed 7) (bound.frame.read (handle "0x1"))
      | .error _ => false
  | .error _ => false

private def sequentialLocals : Bool :=
  match opened with
  | .ok frame =>
      let first := frame.declareLocalInitialized 4 (handle "0x1") intType intType
        (.literal (signed 3))
      match first.result with
      | .ok _ =>
          let second := first.frame.declareLocalInitialized 8 (handle "0x2") intType intType
            (.binary .add (.read (handle "0x1")) (.literal (signed 1)))
          match second.result with
          | .ok _ => okValue (signed 4) (second.frame.read (handle "0x2"))
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def nestedShadow : Bool :=
  match opened with
  | .ok frame =>
      let outer := frame.declareParameter (handle "0x1") intType (signed 7)
      match outer.result with
      | .ok _ =>
          let nested := outer.frame.enterScope
          let inner := nested.frame.declareParameter (handle "0x2") intType (signed 9)
          match inner.result with
          | .ok _ =>
              let exited := inner.frame.exitScope
              okUnit exited &&
                okValue (signed 7) (exited.frame.read (handle "0x1")) &&
                match (exited.frame.read (handle "0x2")).result with
                | .error (.missingBinding declaration) => declaration == handle "0x2"
                | _ => false
          | .error _ => false
      | .error _ => false
  | .error _ => false

def callableNestedShadowWitness : Bool := nestedShadow

private def freshLoopObjects : Bool :=
  match opened with
  | .ok frame =>
      let firstScope := frame.enterScope
      let first := firstScope.frame.declareLocalInitialized 2 (handle "0x1") intType intType
        (.literal (signed 1))
      match first.result with
      | .ok firstObject =>
          let afterFirst := first.frame.exitScope
          let secondScope := afterFirst.frame.enterScope
          let second := secondScope.frame.declareLocalInitialized 2 (handle "0x2") intType intType
            (.literal (signed 2))
          match second.result with
          | .ok secondObject =>
              firstObject != secondObject &&
                objectPhase? second.frame secondObject == some .aliveInitialized &&
                objectPhase? afterFirst.frame firstObject == some .ended
          | .error _ => false
      | .error _ => false
  | .error _ => false

def callableFreshLoopObjectWitness : Bool := freshLoopObjects

private def reentrySameDeclarationFresh : Bool :=
  match opened with
  | .ok frame =>
      let first := frame.declareLocalInitialized 2 (handle "0x1") intType intType
        (.literal (signed 1))
      match first.result with
      | .ok firstObject =>
          let exited := first.frame.exitScope
          let entered := exited.frame.enterScope
          let second := entered.frame.declareLocalInitialized 2 (handle "0x1") intType intType
            (.literal (signed 2))
          match second.result with
          | .ok secondObject => firstObject != secondObject &&
              objectPhase? second.frame firstObject == some .ended &&
              objectPhase? second.frame secondObject == some .aliveInitialized
          | .error _ => false
      | .error _ => false
  | .error _ => false

private def nestedDuplicateHandleRefuses : Bool :=
  match opened with
  | .ok frame =>
      let outer := frame.declareParameter (handle "0x1") intType (signed 7)
      match outer.result with
      | .ok outerObject =>
          let nested := outer.frame.enterScope
          let before := nested.frame.store.objects.objects.length
          let duplicate := nested.frame.declareLocalDefault (handle "0x1") intType
          let after := duplicate.frame.store.objects.objects.length
          (match duplicate.result with
          | .error (.duplicateBinding declaration) => declaration == handle "0x1"
          | _ => false) &&
            before == after &&
            outerObject == 0 &&
            okValue (signed 7) (duplicate.frame.read (handle "0x1")) &&
            duplicate.frame.scopeDepth == 2
      | .error _ => false
  | .error _ => false

private def selfInitializerRefusesAndRetains : Bool :=
  match opened with
  | .ok frame =>
      let declared := frame.declareLocalInitialized 4 (handle "0x1") intType intType
        (.read (handle "0x1"))
      match declared.result with
      | .error (.object (.lifetime .lifetimeNotStarted)) =>
          declared.frame.bound (handle "0x1") &&
            (declared.frame.scopes.head?.bind (fun scope => scope.bindings.head?)).isSome &&
            objectPhase? declared.frame 0 == some .storageOnly
      | .error _ => false
      | .ok _ => false
  | .error _ => false

private def defaultThenAssign : Bool :=
  match opened with
  | .ok frame =>
      let declared := frame.declareLocalDefault (handle "0x1") intType
      match declared.result with
      | .ok _ =>
          let unread := declared.frame.read (handle "0x1")
          let assigned := declared.frame.assignValue (handle "0x1") intType (signed 11)
          (match unread.result with
          | .error (.object (.lifetime .notInitialized)) => true
          | _ => false) && okUnit assigned &&
            okValue (signed 11) (assigned.frame.read (handle "0x1"))
      | .error _ => false
  | .error _ => false

def callableDefaultThenAssignWitness : Bool := defaultThenAssign

private def prefixRetainedAfterInitializerFailure : Bool :=
  match opened with
  | .ok frame =>
      let first := frame.declareLocalInitialized 2 (handle "0x1") intType intType
        (.literal (signed 5))
      match first.result with
      | .ok _ =>
          let failed := first.frame.declareLocalInitialized 2 (handle "0x2") intType intType
            (.binary .divide (.read (handle "0x1")) (.literal (signed 0)))
          (match failed.result with
          | .error (.undefined .divisionByZero) => true
          | _ => false) &&
            okValue (signed 5) (failed.frame.read (handle "0x1")) &&
            failed.frame.bound (handle "0x2") &&
            objectPhase? failed.frame 1 == some .storageOnly
      | .error _ => false
  | .error _ => false

private def reverseCleanup : Bool :=
  match opened with
  | .ok frame =>
      let first := frame.declareLocalInitialized 2 (handle "0x1") intType intType
        (.literal (signed 1))
      let second := first.frame.declareLocalInitialized 2 (handle "0x2") intType intType
        (.literal (signed 2))
      match first.result, second.result with
      | .ok firstObject, .ok secondObject =>
          let exited := second.frame.exitScope
          okUnit exited &&
            objectPhase? exited.frame secondObject == some .ended &&
            objectPhase? exited.frame firstObject == some .ended &&
            exited.frame.scopeDepth == 0
      | _, _ => false
  | .error _ => false

def callableReverseCleanupWitness : Bool := reverseCleanup

private def returnClosesFrame : Bool :=
  match opened with
  | .ok frame =>
      let declared := frame.declareLocalInitialized 2 (handle "0x1") intType intType
        (.literal (signed 13))
      match declared.result with
      | .ok _ =>
          let returned := declared.frame.returnValue 4 (.read (handle "0x1"))
          (match returned.result with
          | .ok value => value == signed 13
          | _ => false) && returned.frame.scopeDepth == 0 &&
            objectPhase? returned.frame 0 == some .ended
      | .error _ => false
  | .error _ => false

def callableReturnClosesFrameWitness : Bool := returnClosesFrame

private def duplicateAndMissingAreLoud : Bool :=
  match opened with
  | .ok frame =>
      let first := frame.declareParameter (handle "0x1") intType (signed 1)
      let duplicate := first.frame.declareLocalDefault (handle "0x1") intType
      let missing := first.frame.read (handle "0x9")
      (match first.result with | .ok object => object == 0 | _ => false) &&
        (match duplicate.result with
        | .error (.duplicateBinding declaration) => declaration == handle "0x1"
        | _ => false) &&
        (match missing.result with
        | .error (.missingBinding declaration) => declaration == handle "0x9"
        | _ => false)
  | .error _ => false

private def noScopeIsLoud : Bool :=
  match IntegralObjectFrame.empty .lp64 with
  | .ok frame =>
      let declared := frame.declareLocalDefault (handle "0x1") intType
      (match declared.result with | .error .noActiveScope => true | _ => false) &&
        declared.frame.store.objects.objects.isEmpty
  | .error _ => false

private def constAndDurationChecks : Bool :=
  match opened with
  | .ok frame =>
      let declaredLocal := frame.declareLocalInitialized 2 (handle "0x1")
        (.qualified true false intType) intType (.literal (signed 3))
      match declaredLocal.result with
      | .ok _ =>
          let write := declaredLocal.frame.assignValue (handle "0x1") intType (signed 4)
          match write.result with
          | .error (.object .constWrite) => true
          | _ => false
      | .error _ => false
  | .error _ => false

private def executeReturnCleans : Bool :=
  match opened with
  | .ok frame =>
      let statement := .sequence
        (.declare (handle "0x1") intType intType (.literal (signed 13)))
        (.return_ (.read (handle "0x1")))
      let result := frame.execute 12 statement
      (match result.result with
      | .ok (some value) => value == signed 13
      | _ => false) && result.frame.scopeDepth == 0 &&
        objectPhase? result.frame 0 == some .ended
  | .error _ => false

private def executeBlockScopes : Bool :=
  match opened with
  | .ok frame =>
      let parameter := frame.declareParameter (handle "0x1") intType (signed 4)
      match parameter.result with
      | .ok _ =>
          let statement := .block
            (.sequence
              (.declare (handle "0x2") intType intType
                (.binary .add (.read (handle "0x1")) (.literal (signed 1))))
              (.expression (.read (handle "0x2"))))
          let result := parameter.frame.execute 12 statement
          (match result.result with | .ok none => true | _ => false) &&
            result.frame.scopeDepth == 0 && objectPhase? result.frame 1 == some .ended
      | .error _ => false
  | .error _ => false

private def executeForScope : Bool :=
  match opened with
  | .ok frame =>
      let statement := .forLoop
        (.declare (handle "0x1") intType intType (.literal (signed 3)))
        (.read (handle "0x1"))
        (.assign (handle "0x1") intType
          (.binary .subtract (.read (handle "0x1")) (.literal (signed 1))))
        (.block (.expression (.read (handle "0x1"))))
      let result := frame.execute 64 statement
      (match result.result with | .ok none => true | _ => false) &&
        result.frame.scopeDepth == 0 && objectPhase? result.frame 0 == some .ended
  | .error _ => false

private def executeContinueAndBreak : Bool :=
  match opened with
  | .ok frame =>
      let statement := .whileLoop (.literal (⟨.boolean, 1⟩ : IntegralValue))
        (.block (.sequence .break_ .continue_))
      let result := frame.execute 12 statement
      (match result.result with | .ok none => true | _ => false) && result.frame.scopeDepth == 0
  | .error _ => false

private def executeFailureRetainsScope : Bool :=
  match opened with
  | .ok frame =>
      let statement := .block
        (.sequence
          (.declare (handle "0x1") intType intType (.literal (signed 5)))
          (.expression (.binary .divide (.literal (signed 1)) (.literal (signed 0)))))
      let result := frame.execute 12 statement
      (match result.result with
      | .error (.undefined .divisionByZero) => true
      | _ => false) && result.frame.scopeDepth == 2 && result.frame.bound (handle "0x1")
  | .error _ => false

def temporaryReferenceLifecycle : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let bound := frame.bindTemporaryReference 8 (handle "0x1")
        (.lvalueReference (.qualified true false intType)) (.builtin .short)
        (.literal ⟨.signed 16, 9⟩)
      match bound.result with
      | .error _ => false
      | .ok object =>
          let read := bound.frame.read (handle "0x1")
          let write := bound.frame.assignValue (handle "0x1") intType (signed 10)
          let exited := bound.frame.exitScope
          objectPhase? bound.frame object == some .aliveInitialized &&
            okValue (signed 9) read &&
            (write.result matches .error (.object .constWrite)) &&
            okUnit exited && objectPhase? exited.frame object == some .ended &&
            (exited.frame.read (handle "0x1")).result matches
              .error (.missingBinding _)

def zeroInitializationLifecycle : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let declared := frame.declareLocalZero (handle "0x1")
        (.qualified true false intType)
      let constDeclared := declared.frame.declareLocalZero (handle "0x2") intType
      match declared.result, constDeclared.result with
      | .ok object, .ok constObject =>
          objectPhase? constDeclared.frame object == some .aliveInitialized &&
            objectPhase? constDeclared.frame constObject == some .aliveInitialized &&
            okValue (signed 0) (constDeclared.frame.read (handle "0x1")) &&
            okValue (signed 0) (constDeclared.frame.read (handle "0x2"))
      | _, _ => false

def staticLocalLifecycle : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let first := frame.declareStaticInitialized 8 (handle "0x1") intType intType
        (.literal (signed 3))
      match first.result with
      | .error _ => false
      | .ok object =>
          let exited := first.frame.exitScope
          let entered := exited.frame.enterScope
          let second := entered.frame.declareStaticInitialized 8 (handle "0x1") intType intType
            (.literal (signed 99))
          match second.result with
          | .ok reused =>
              let closed := second.frame.exitScope
              object == reused &&
                objectPhase? second.frame object == some .aliveInitialized &&
                okValue (signed 3) (second.frame.read (handle "0x1")) &&
                okUnit closed && objectPhase? closed.frame object == some .aliveInitialized &&
                closed.frame.staticBindings.length == 1
          | .error _ => false

private def staticLocalStatement : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let first := frame.execute 8 (.staticDeclare (handle "0x1") intType intType
        (.literal (signed 4)))
      let entered := first.frame.enterScope
      let second := entered.frame.execute 8 (.staticDeclare (handle "0x1") intType intType
        (.literal (signed 8)))
      (first.result matches .ok none) && (second.result matches .ok none) &&
        second.frame.staticBindings.length == 1 &&
        second.frame.store.values == [some (signed 4)] &&
        objectPhase? second.frame 0 == some .aliveInitialized

def threadLocalLifecycle : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let first := frame.declareThreadInitialized 8 (handle "0x1") intType intType
        (.literal (signed 5))
      match first.result with
      | .error _ => false
      | .ok object =>
          let exited := first.frame.exitScope
          let entered := exited.frame.enterScope
          let second := entered.frame.declareThreadInitialized 8 (handle "0x1") intType intType
            (.literal (signed 77))
          match second.result with
          | .ok reused =>
              let closed := second.frame.exitScope
              object == reused &&
                objectPhase? second.frame object == some .aliveInitialized &&
                okValue (signed 5) (second.frame.read (handle "0x1")) &&
                okUnit closed && objectPhase? closed.frame object == some .aliveInitialized &&
                closed.frame.threadBindings.length == 1 &&
                closed.frame.store.threadBindings.length == 1
          | .error _ => false

private def threadLocalStatement : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let first := frame.execute 8 (.threadDeclare (handle "0x1") intType intType
        (.literal (signed 6)))
      let entered := first.frame.enterScope
      let second := entered.frame.execute 8 (.threadDeclare (handle "0x1") intType intType
        (.literal (signed 9)))
      (first.result matches .ok none) && (second.result matches .ok none) &&
        second.frame.threadBindings.length == 1 &&
        second.frame.store.values == [some (signed 6)] &&
        objectPhase? second.frame 0 == some .aliveInitialized

def dynamicLocalLifecycle : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let declared := frame.declareDynamicInitialized 8 (handle "0x1") intType intType
        (.literal (signed 7))
      match declared.result with
      | .error _ => false
      | .ok object =>
          let before := declared.frame.read (handle "0x1")
          let leaked := declared.frame.exitScope
          let released := declared.frame.releaseDynamic (handle "0x1")
          let closed := released.frame.exitScope
          okValue (signed 7) before &&
            (leaked.result matches .ok ()) &&
            objectPhase? leaked.frame object == some .aliveInitialized &&
            (released.result matches .ok ()) &&
            (released.frame.read (handle "0x1")).result matches
              .error (.object (.lifetime .storageReleased)) &&
            okUnit closed && objectPhase? closed.frame object == some .released

private def dynamicLocalStatement : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let declared := frame.executeOpen 8 (.dynamicDeclare (handle "0x1") intType intType
        (.literal (signed 8)))
      let released := declared.frame.executeOpen 8 (.dynamicRelease (handle "0x1"))
      let closed := released.frame.exitScope
      (declared.result matches .ok none) && (released.result matches .ok none) &&
        (closed.result matches .ok ()) && objectPhase? closed.frame 0 == some .released

private def temporaryReferenceStatement : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let result := frame.execute 12 (.temporaryReference (handle "0x1")
        (.rvalueReference intType) (.builtin .short) (.literal ⟨.signed 16, 11⟩))
      (result.result matches .ok none) && result.frame.scopeDepth == 0 &&
        objectPhase? result.frame 0 == some .ended

private def temporaryReferenceRefusals : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let mutable := frame.bindTemporaryReference 4 (handle "0x1")
        (.lvalueReference intType) intType (.literal (signed 1))
      let first := frame.bindTemporaryReference 4 (handle "0x1")
        (.rvalueReference intType) intType (.literal (signed 2))
      let duplicate := first.frame.bindTemporaryReference 4 (handle "0x1")
        (.rvalueReference intType) intType (.literal (signed 3))
      (mutable.result matches .error (.temporaryReferenceUnsupported _)) &&
        (first.result matches .ok _) &&
        (duplicate.result matches .error (.duplicateBinding _))
private def executeOutsideTransferLoud : Bool :=
  match opened with
  | .ok frame =>
      let broken := frame.execute 4 .break_
      let continued := frame.execute 4 .continue_
      (match broken.result with | .error .breakOutsideLoop => true | _ => false) &&
        (match continued.result with | .error .continueOutsideLoop => true | _ => false) &&
        broken.frame.scopeDepth == 0 && continued.frame.scopeDepth == 0
  | .error _ => false

#guard parameterRead
#guard sequentialLocals
#guard nestedShadow
#guard freshLoopObjects
#guard reentrySameDeclarationFresh
#guard nestedDuplicateHandleRefuses
#guard selfInitializerRefusesAndRetains
#guard defaultThenAssign
#guard prefixRetainedAfterInitializerFailure
#guard reverseCleanup
#guard returnClosesFrame
#guard duplicateAndMissingAreLoud
#guard noScopeIsLoud
#guard constAndDurationChecks
#guard executeReturnCleans
#guard executeBlockScopes
#guard executeForScope
#guard executeContinueAndBreak
#guard executeFailureRetainsScope
#guard executeOutsideTransferLoud
#guard temporaryReferenceLifecycle
#guard zeroInitializationLifecycle
#guard staticLocalLifecycle
#guard staticLocalStatement
#guard threadLocalLifecycle
#guard threadLocalStatement
#guard dynamicLocalLifecycle
#guard dynamicLocalStatement
#guard temporaryReferenceStatement
#guard temporaryReferenceRefusals

#guard match IntegralObjectFrame.empty .lp64 with
  | .ok frame => okUnit frame.enterScope
  | .error _ => false

#guard IntegralObjectFrame.empty {TargetProfile.lp64 with intWidth := 8} matches
  .error .invalidProfile

-- Conversion precedes the operator, including promotion of the signed minimum.
#guard match opened with
  | .ok frame =>
      ((frame.evaluate 4 (.unary .negate
        (.convert (.signed 32) (.literal ⟨.signed 16, -32768⟩)))).result matches
          .ok (.ok ⟨.signed 32, 32768⟩))
  | .error _ => false

#guard match opened with
  | .ok frame =>
      ((frame.evaluate 4 (.unary .logicalNot
        (.convert .boolean (.literal (signed 2))))).result matches .ok (.ok ⟨.boolean, 0⟩))
  | .error _ => false

-- A conversion must retain a failed operand instead of fabricating a value.
#guard match opened with
  | .ok frame =>
      ((frame.evaluate 4 (.convert (.signed 32)
        (.binary .divide (.literal (signed 1)) (.literal (signed 0))))).result matches
          .ok (.undefined .divisionByZero))
  | .error _ => false

#guard match opened with
  | .ok frame =>
      let result := frame.evaluate 3 (.convert .boolean (.read (handle "0x99")))
      result.frame == frame && (result.result matches .error (.missingBinding _))
  | .error _ => false

-- These are kernel-reduction regressions; #guard alone executes native code.
private def cleanupFailureRetainsPrefix : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let outer := frame.declareParameter (handle "0x1") intType (signed 7)
      let nested := outer.frame.enterScope
      let first := nested.frame.declareParameter (handle "0x2") intType (signed 8)
      let second := first.frame.declareParameter (handle "0x3") intType (signed 9)
      match first.result, second.result with
      | .ok firstObject, .ok secondObject =>
          match second.frame.store.endLifetime firstObject with
          | .error _ => false
          | .ok store =>
              let before := {second.frame with store}
              let closed := before.leaveFrame
              (closed.result matches .error (.object (.lifetime .lifetimeEnded))) &&
                closed.frame.scopes == before.scopes &&
                objectPhase? closed.frame secondObject == some .ended &&
                okValue (signed 7) (closed.frame.read (handle "0x1"))
      | _, _ => false

#guard cleanupFailureRetainsPrefix

example (frame : IntegralObjectFrame) (expression : Expression) :
    frame.evaluate 0 expression = {frame, result := .error .fuelExhausted} := rfl

private theorem kernelFrameExecution :
    (sequentialLocals && reverseCleanup && cleanupFailureRetainsPrefix && executeForScope &&
      executeContinueAndBreak && executeFailureRetainsScope) = true := rfl

#print axioms kernelFrameExecution

private def aliasLifetimeAndConst : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let parameter := frame.declareParameter (handle "0x1") intType (signed 7)
      let nested := parameter.frame.enterScope
      let alias := nested.frame.bindLocalReference (handle "0x2")
        (.lvalueReference intType) (handle "0x1")
      let view := alias.frame.bindLocalReference (handle "0x3")
        (.lvalueReference (.qualified true false intType)) (handle "0x2")
      let written := view.frame.assignValue (handle "0x2") intType (signed 9)
      let constWrite := written.frame.assignValue (handle "0x3") intType (signed 10)
      let dropConst := written.frame.bindLocalReference (handle "0x4")
        (.lvalueReference intType) (handle "0x3")
      let closed := written.frame.exitScope
      let finished := closed.frame.leaveFrame
      parameter.result.toOption == some 0 && alias.result.toOption == some 0 && view.result.toOption == some 0 &&
        alias.frame.store == nested.frame.store && view.frame.store == alias.frame.store &&
        written.frame.store.objects.objects.length == 1 &&
        okValue (signed 9) (written.frame.read (handle "0x1")) &&
        okValue (signed 9) (written.frame.read (handle "0x3")) &&
        (constWrite.result matches .error (.object .constWrite)) &&
        constWrite.frame == written.frame &&
        (dropConst.result matches .error (.object .referenceQualification)) &&
        dropConst.frame == written.frame && okUnit closed &&
        okValue (signed 9) (closed.frame.read (handle "0x1")) &&
        !closed.frame.bound (handle "0x2") && !closed.frame.bound (handle "0x3") &&
        okUnit finished && objectPhase? finished.frame 0 == some .ended

private def aliasUninitializedAndEnded : Bool :=
  match opened with
  | .error _ => false
  | .ok frame =>
      let object := frame.declareLocalDefault (handle "0x1") intType
      let alias := object.frame.bindLocalReference (handle "0x2")
        (.lvalueReference intType) (handle "0x1")
      let beforeWrite := alias.frame.read (handle "0x2")
      let assigned := alias.frame.assignValue (handle "0x2") intType (signed 11)
      let duplicate := assigned.frame.bindLocalReference (handle "0x2")
        (.lvalueReference intType) (handle "0x1")
      let closed := assigned.frame.leaveFrame
      let afterEnd := {alias.frame with store := closed.frame.store}
      let stale := afterEnd.read (handle "0x2")
      let lateBinding := afterEnd.bindLocalReference (handle "0x3")
        (.lvalueReference intType) (handle "0x2")
      alias.result.toOption == some 0 && alias.frame.store == object.frame.store &&
        (beforeWrite.result matches .error (.object (.lifetime .notInitialized))) &&
        okValue (signed 11) (assigned.frame.read (handle "0x1")) &&
        (duplicate.result matches .error (.duplicateBinding _)) &&
        duplicate.frame == assigned.frame && okUnit closed &&
        (stale.result matches .error (.object (.lifetime .lifetimeEnded))) &&
        (lateBinding.result matches .error (.object (.lifetime .lifetimeEnded))) &&
        lateBinding.frame == afterEnd

def callableLocalReferenceWitness : Bool := aliasLifetimeAndConst && aliasUninitializedAndEnded

#guard aliasLifetimeAndConst
#guard aliasUninitializedAndEnded
#guard callableLocalReferenceWitness
#guard callableReturnClosesFrameWitness
#guard callableReverseCleanupWitness
#guard callableDefaultThenAssignWitness
#guard callableFreshLoopObjectWitness
#guard callableNestedShadowWitness

private theorem kernelReferenceBindings :
    (aliasLifetimeAndConst && aliasUninitializedAndEnded) = true := rfl

theorem callable_local_reference_witness : callableLocalReferenceWitness = true := by
  rfl

#print axioms kernelReferenceBindings
#print axioms callable_local_reference_witness
#print axioms IntegralObjectFrame.bindLocalReference_store

end LeanModels.Cpp.IntegralObjectFrameTests
