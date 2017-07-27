Store = {Dictionary.new}
CurrentIndex = {NewCell 0}

fun {AddKeyToSAS}
    CurrentIndex := @CurrentIndex + 1
    {Dictionary.put Store @CurrentIndex equivalence(@CurrentIndex)}
    @CurrentIndex
end

fun {RetrieveFromSAS Key}
    local Value in
        Value = {Dictionary.get Store Key}
        case Value
        of equivalence(X) then equivalence(X)
        [] reference(X) then {RetrieveFromSAS X}
        else Value
        end
    end
end

fun {IsFree Key}
    local Value in
        Value = {RetrieveFromSAS Key}
        case Value
        of equivalence(X) then true
        else false
        end
    end
end

proc {BindValueToKeyInSAS Key Val}
    {Dictionary.put Store Key Val}
end

proc {BindRefToKeyInSAS Key RefKey}
    {Dictionary.put Store Key reference(RefKey)}
end
