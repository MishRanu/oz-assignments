MultiStack = {NewCell nil}
SuspendCount = {NewCell 0}
%thread level
proc {AddNewStack StmtEnvPair}
    MultiStack := [StmtEnvPair] | @MultiStack
end

proc {DeleteCurSemanticStack}
    MultiStack := @MultiStack.2
end

proc {SuspendCurrentThread}
    MultiStack := {Append @MultiStack.2 [@MultiStack.1]}
    {IncreaseSuspendCount}
    if @SuspendCount == {Length @MultiStack} then raise allThreadSuspended end else skip end
end

proc {ResetSuspendCount}
    SuspendCount := 0
end

proc {IncreaseSuspendCount}
    SuspendCount := @SuspendCount + 1
end

%statement level
proc {Push StmtEnvPair}
    MultiStack := (StmtEnvPair|@MultiStack.1) | @MultiStack.2
end

fun {Pop}
    case @MultiStack.1
    of nil then
        {DeleteCurSemanticStack}
        nil
    [] StmtEnvPair | RemainingStack then
        MultiStack := RemainingStack | @MultiStack.2
        StmtEnvPair
    end
end
