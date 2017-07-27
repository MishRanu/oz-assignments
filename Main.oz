% Assignment 3 : Threads in interpreter for Kernel Language
% Authors: Abhilash (12014), Anusha (12148), Saurav (12641)
% Compilation: This codes compiles stand-alone using ozc compiler
% Compile: ` ozc -c Main.oz -f Main `
% Run : ` ozengine Main `

functor
import
    Browser(browse: Browse)
define
    % Stack < Statement, Environment > Pair of stmt and env
    \insert 'SemanticStack.oz'
    \insert 'SingleAssignmentStore.oz'
    \insert 'ProcessRecords.oz'
    \insert 'Unify.oz'

    Current = {NewCell nil}
    fun {Declare X Env}
        case X
        of ident(X1) then {Adjoin Env env(X1:{AddKeyToSAS})}
        [] [record Label Features] then
            {DeclareListItems Features Env}
        else raise declarationError(X) end
        end
    end

    fun {DeclareListItems ListItems Env}
        case ListItems
        of nil then Env
        [] [literal(_) ident(X)] | Items then
            {DeclareListItems Items {Declare ident(X) Env}}
        else raise illFormedRecord(ListItems) end
        end
    end

    fun {GetIdent Stmt}
        {Filter {Flatten Stmt} (fun {$ X} case X of ident(_) then true else false end end)}
    end

    fun {GetCeVars Identifiers Env}
        {Filter {Map Identifiers (fun {$ X} case X of ident(Y) then Y else nil end end)}
                (fun {$ X} {HasFeature Env X} end)
        }
    end

    fun {CreateCe FinalCeVars Env}
        {FoldR FinalCeVars (fun {$ X Y} {Adjoin Y env(X:Env.X)} end) env()}
    end

    % CE = (identifiers in Stmt "intersection" identifiers in Env) - (identifiers in ParamList)
    fun {GetCE Stmt ParamList Env}
        % Env % TODO complete this correctly
        local Identifiers IdentNames NewEnv TempVars FinalCeVars in
            Identifiers = {GetIdent Stmt} % [ident(x) ident(y)]
            TempVars = {GetCeVars Identifiers Env} % [x y]
            % ParamList : [ident(u) ident(v)]
            IdentNames = {Map ParamList (fun {$ X} case X of ident(Y) then Y else nil end end)} % [u v]
            FinalCeVars = {Filter TempVars (fun {$ X} if {Member X IdentNames} then false else true end end)}
            % FinalCeVars = [x y]
            {CreateCe FinalCeVars Env}
        end
    end

    fun {GenEnvForFunction NewEnv ActualParams FormalParams Env}
        case ActualParams#FormalParams
        of (ident(A)|As)#(ident(F)|Fs) then
            {GenEnvForFunction {Adjoin NewEnv env(F:Env.A)} As Fs Env}
        else NewEnv
        end
    end

    proc {Interpret AST}
        local Execute Loop in
            % Procedure to execute top statement on semantic stack
            proc {Execute}
                Current := {Pop}
                {Browse @Current}
                % {Browse {Dictionary.toRecord store Store}}
                if @Current \= nil then
                    case @Current.stmt
                    of nil then {Browse 'Complete'}
                    % 'nop' : skip. Do nothing
                    [] [nop] then {ResetSuspendCount} {Execute}
                    % 'local block declaration': Push S, add X to env
                    [] [localvar X S] then
                        {Push sepair(stmt:S env:{Declare X @Current.env})}
                        {ResetSuspendCount}
                        {Execute}
                    % 'bind operation' using unification
                    [] [bind X Y] then
                        case Y
                        of [procedure ParamList S] then
                            % put procedure with its CE into SAS as a record
                            {Unify X procedure(params:ParamList stmt:S env:{GetCE S ParamList @Current.env}) @Current.env}
                        else
                            {Unify X Y @Current.env}
                        end
                        {ResetSuspendCount}
                        {Execute}
                    % 'if-then-else'
                    [] [conditional ident(P) S1 S2] then
                        if {IsFree @Current.env.P} then
                            {Push @Current}
                            {SuspendCurrentThread}
                        else
                            {ResetSuspendCount}
                            local Predicate in
                                Predicate = {RetrieveFromSAS @Current.env.P}
                                if Predicate == literal(true) then
                                    {Push sepair(stmt:S1 env:@Current.env)}
                                else
                                    if Predicate == literal(false) then
                                        {Push sepair(stmt:S2 env:@Current.env)}
                                    else raise conditionNotBoolean(P) end
                                    end
                                end
                            end
                        end
                        {Execute}
                    % 'case x of p then s1 else s2 end'
                    [] [match ident(X) P S1 S2] then
                        if {IsFree @Current.env.X} then
                            {Push @Current}
                            {SuspendCurrentThread}
                        else
                            {ResetSuspendCount}
                            try % if unification fails, do S2
                                local NewEnv in
                                    NewEnv = {Declare P @Current.env}
                                    {Unify ident(X) P NewEnv} % P==X ? S1 : S2
                                    {Push sepair(stmt:S1 env:NewEnv)}
                                end
                            catch incompatibleTypes(_ _) then
                                {Push sepair(stmt:S2 env:@Current.env)}
                            end
                        end
                        {Execute}
                    % 'function application'
                    [] apply | ident(F) | Params then
                        if {IsFree @Current.env.F} then
                            {Push @Current}
                            {SuspendCurrentThread}
                            {Execute}
                        else
                            {ResetSuspendCount}
                            local Function FormalParams NewEnv in
                                Function = {RetrieveFromSAS @Current.env.F}
                                FormalParams = Function.params
                                if {Length FormalParams} == {Length Params} then skip
                                else raise unequalParamList(F) end
                                end
                                NewEnv = {GenEnvForFunction Function.env Params FormalParams @Current.env}
                                {Push sepair(stmt:Function.stmt env:NewEnv)}
                                {Execute}
                            end
                        end
                    % 'thread statement'
                    [] [thrd S] then
                        {ResetSuspendCount}
                        {AddNewStack sepair(stmt:S env:@Current.env)}
                        {Execute}
                    % S -> S1 S2. Push S2 first. Then S1
                    [] X|Xr then
                        if Xr \= nil then
                            {Push sepair(stmt:Xr env:@Current.env)}
                        else skip end
                        {Push sepair(stmt:X env:@Current.env)}
                        {ResetSuspendCount}
                        {Execute}
                    end
                else
                    {Browse 'Completed a Thread'}
                    {Loop}
                end
            end
            proc {Loop}
                if @MultiStack == nil then {Browse 'done!'} else {Execute} end
            end
            {AddNewStack sepair(stmt:AST env:nil)}
            {Loop}
        end
    end
    % ------------------------------------ Test Cases ------------------------------------
    % Threads
    % {Interpret [thrd [[nop] [nop] [nop]]]}
    % Problem 1
    % {Interpret [[[[nop]]]]}
    % {Interpret [[nop] [nop] [nop]]}

    % Problem 2
    % {Interpret [[nop] [localvar ident(x) [nop]] [nop]]}
    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [
    %                         [localvar ident(x)
    %                             [nop]
    %                         ]
    %                         [nop]
    %                     ]
    %                 ]
    %             ]}

    % Problem 3
    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [bind ident(x) ident(y)]
    %                 ]
    %             ]}

    % Problem 4a
    % {Interpret  [localvar ident(x)
    %                 [bind ident(x) [record literal(a) [literal(f1) ident(x)]]]
    %             ]}
    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [
    %                         [bind ident(x) [record literal(a) [[literal(f1) ident(y)]]]]
    %                         [bind ident(y) literal(100)]
    %                     ]
    %                 ]
    %             ]}

    % Problem 5a
    % {Interpret  [localvar ident(x)
    %                 [bind ident(x) literal(100)]
    %             ]}

    % Problem 6
    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [
    %                         [bind ident(x) literal(true)]
    %                         [conditional ident(x)
    %                             [bind ident(y) literal(42)]
    %                             [bind ident(y) literal(0)]
    %                         ]
    %                     ]
    %                 ]
    %             ]}

    % Threads
    {Interpret  [localvar ident(x)
                [localvar ident(y)
                    [
                        [thrd [bind ident(x) literal(true)]]
                        [conditional ident(x)
                            [bind ident(y) literal(42)]
                            [bind ident(y) literal(0)]
                        ]
                    ]
                ]
            ]}

    % all threads get suspended
        % {Interpret  [localvar ident(x)
        %         [localvar ident(y)
        %             [
        %                 [thrd [conditional ident(x)
        %                     [bind ident(y) literal(true)]
        %                     [bind ident(y) literal(false)]
        %                 ]]
        %                 [thrd [conditional ident(y)
        %                     [bind ident(x) literal(true)]
        %                     [bind ident(x) literal(false)]
        %                 ]]
        %             ]
        %         ]
        %     ]}



    % Problem 7
    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [localvar ident(z)
    %                         [
    %                             [bind ident(x) [record literal(a) [[literal(f1) literal(100)]]]]
    %                             [match ident(x) [record literal(a) [[literal(f1) ident(n)]]]
    %                                 [bind ident(z) literal(42)]
    %                                 [bind ident(z) literal(0)]
    %                             ]
    %                         ]
    %                     ]
    %                 ]
    %             ]}
    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [localvar ident(z)
    %                         [
    %                             [bind ident(x) [record literal(a) [[literal(f1) literal(100)]]]]
    %                             [match ident(x) [record literal(b) [[literal(f1) ident(y)]]]
    %                                 [bind ident(z) literal(42)]
    %                                 [bind ident(z) literal(0)]
    %                             ]
    %                         ]
    %                     ]
    %                 ]
    %             ]}

    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [localvar ident(z)
    %                         [
    %                             [bind ident(x) [record literal(a) [
    %                                 [literal(f1) literal(100)]
    %                                 [literal(f2) [record literal(b) [
    %                                     [literal(f3) literal(42)]
    %                                 ]]]
    %                             ]]]
    %                             [match ident(x) [record literal(b) [[literal(f1) ident(y)]]]
    %                                 [bind ident(z) literal(42)]
    %                                 [bind ident(z) literal(0)]
    %                             ]
    %                         ]
    %                     ]
    %                 ]
    %             ]}

    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [localvar ident(z)
    %                         [
    %                             [bind ident(y) literal(80)]
    %                             [bind ident(x) [record literal(a) [
    %                                 [literal(f1) ident(y)]
    %                                 [literal(f2) [record literal(b) [
    %                                     [literal(f3) ident(y)]
    %                                 ]]]
    %                             ]]]
    %                             [match ident(x) [record literal(a) [
    %                                                 [literal(f1) ident(m)]
    %                                                 [literal(f2) ident(n)]
    %                                             ]] % y will bind to record corresponding to literal(b)
    %                                 [bind ident(z) literal(42)]
    %                                 [bind ident(z) literal(0)]
    %                             ]
    %                         ]
    %                     ]
    %                 ]
    %             ]}
    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [localvar ident(z)
    %                         [localvar ident(u)
    %                             [
    %                                 [bind ident(y) literal(80)]
    %                                 [bind ident(u) literal(100)]
    %                                 [bind ident(x) [record literal(a) [
    %                                     [literal(f1) ident(y)]
    %                                     [literal(f2) [record literal(b) [
    %                                         [literal(f3) ident(y)]
    %                                     ]]]
    %                                 ]]]
    %                                 [match ident(x) [record literal(a) [
    %                                                     [literal(f1) ident(u)] % new local u created.
    %                                                     [literal(f2) ident(n)]
    %                                                 ]] % y will bind to record corresponding to literal(b)
    %                                     [bind ident(z) literal(42)]
    %                                     [bind ident(z) literal(0)]
    %                                 ]
    %                             ]
    %                         ]
    %                     ]
    %                 ]
    %             ]}

    % Problem 4b, 5b
    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [localvar ident(z)
    %                         [
    %                             [bind ident(z) literal(100)]
    %                             [bind ident(x)  [procedure [ident(p1)]
    %                                                 [
    %                                                     [nop]
    %                                                     [localvar ident(u)
    %                                                         [bind ident(u) ident(y)]
    %                                                     ]
    %                                                     [localvar ident(v)
    %                                                         [bind ident(v) ident(z)]
    %                                                     ]
    %                                                 ]
    %                                             ]
    %                             ]
    %                         ]
    %                     ]
    %                 ]
    %             ]}

    % Problem 8
    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [localvar ident(z)
    %                         [
    %                             [thrd [bind ident(z) literal(100)]]
    %                             [thrd [apply ident(x) ident(z)]]
    %                             [thrd [bind ident(x)  [procedure [ident(p1)]
    %                                                 [
    %                                                     [nop]
    %                                                     [localvar ident(u)
    %                                                         [bind ident(u) ident(p1)]
    %                                                     ]
    %                                                     [localvar ident(v)
    %                                                         [bind ident(v) ident(z)]
    %                                                     ]
    %                                                 ]
    %                                             ]
    %                             ]]
    %                         ]
    %                     ]
    %                 ]
    %             ]}

    % {Interpret  [localvar ident(x)
    %                 [localvar ident(y)
    %                     [localvar ident(z)
    %                         [
    %                             [thrd [bind ident(z) literal(100)]]
    %                             [thrd [apply ident(x) ident(z)]]
    %                             [bind ident(x)  [procedure [ident(p1)]
    %                                                 [
    %                                                     [nop]
    %                                                     [localvar ident(u)
    %                                                         [bind ident(u) ident(p1)]
    %                                                     ]
    %                                                     [localvar ident(v)
    %                                                         [bind ident(v) ident(z)]
    %                                                     ]
    %                                                 ]
    %                                             ]
    %                             ]
    %                         ]
    %                     ]
    %                 ]
    %             ]}


    % Streaming 1s
    % {Interpret  [localvar ident(oneList)
    %                 [localvar ident(one)
    %                     [
    %                         [bind ident(one) literal(1)]
    %                         [bind ident(oneList)    [record literal(foo)
    %                                                     [literal(f1) ident(one)]
    %                                                     [literal(f2) ident(oneList)]
    %                                                 ]
    %                         ]
    %                     ]
    %                 ]
    %             ]}

    % --------------------------------- Test Cases End ------------------------------------
end
