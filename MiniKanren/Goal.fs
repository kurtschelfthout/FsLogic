namespace MiniKanren

module Goal =

    open MiniKanren.Substitution
    open MiniKanren
    open System
    open Microsoft.FSharp.Quotations

    type Goal = Goal of (Subst -> Stream<Subst>) with 
        static member Subst(Goal g) = g
        static member (&&&)(Goal g1,Goal g2) =
            Goal (g1 >=> g2)
        static member (|||)(Goal g1,Goal g2) =
            Goal <| fun s -> g1 s +++ g2 s

    let (|Goals|) (g:list<_>) = g |> List.map Goal.Subst

    //A goal is a function that maps a substitution to an
    //ordered sequence of zero or more values.
    let equiv (u:'a) (v:'a) : Goal =
        Goal <| fun a -> 
            unify u v a
            |> Option.map Stream.unit
            |> Option.defaultTo Stream.mzero

    //this trick for unification overloading doesn't
    //reallly work well in all cases.
    type Equiv = Equiv with
        static member (?<-)(Equiv, l, v) = 
            equiv l <@ v @>
        static member (?<-)(Equiv, v, r) = 
            equiv <@ v @> r
        static member (?<-)(Equiv, l:Quotations.Expr<'a>,r:Quotations.Expr<'a>) =
            equiv l r
 
    let inline (-=-) l r = Equiv ? (l) <- r

    let all (Goals goals) : Goal =
        let g = goals |> List.head
        let gs = goals |> List.tail
        Goal <| fun a -> Stream.delay (fun () -> (Stream.bindMany (g a) gs))

    let conde (goals:#seq<list<Goal>>) : Goal =
        Goal <| fun a -> 
            Stream.delay (fun () -> 
                (Stream.mplusMany (goals |> Seq.map (fun ((Goal g)::(Goals gs)) -> 
                    Stream.bindMany (g a) gs) |> Seq.toList)))

    let conda (goals:list<list<Goal>>) : Goal = 
        let rec ifa subst = function
            | [] | [[]] -> Stream.mzero
            | ((Goal g0)::(Goals g))::gs ->
                let rec loop = function
                    | MZero -> ifa subst gs
                    | Inc f -> loop f.Value
                    | Unit _  
                    | Choice (_,_) as a-> Stream.bindMany a g
                loop (g0 subst)
        Goal <| fun subst -> ifa subst goals

    let condu (goals:list<list<Goal>>) : Goal = 
        let rec ifu subst = function
            | [] | [[]] -> Stream.mzero
            | ((Goal g0)::(Goals g))::gs ->
                let rec loop = function
                    | MZero -> ifu subst gs
                    | Inc f -> loop f.Value
                    | Unit _ as a -> Stream.bindMany a g
                    | Choice (a,_) -> Stream.bindMany (Stream.unit a) g
                loop (g0 subst)
        Goal <| fun subst -> ifu subst goals

    let inline recurse fg =
        Goal <| fun a -> Stream.delay (fun () -> let (Goal g) = fg() in g a)

    let rec fix f x = fun a -> Stream.delay (fun () -> (f (fix f) x a))

    let rec take n f =
        if n = 0 then 
            []
        else
            match f with
            | MZero -> []
            | Inc (Lazy s) -> take n s
            | Unit a -> [a]
            | Choice(a,f) ->  a :: take (n-1) f

    let inline run n (f: _ -> Goal) =
        Stream.delay (fun () -> let x = fresh()
                                (Goal.Subst (f x) Map.empty) >>= (reify x >> Stream.unit))
        |> take n

    let inline runEval n (f: _ -> Goal) =
        run n f
        |> List.map Swensen.Unquote.Operators.evalRaw

    let inline runShow n (f: _ -> Goal) =
        run n f
        |> Seq.map Swensen.Unquote.Operators.decompile
        |> String.concat Environment.NewLine

    //impure operators
    let project (v:Expr<'a>) (f:'a -> Goal) : Goal =
        Goal <| fun s -> 
            //assume atom here..otherwise fail
            let x = walkMany v s
            Goal.Subst (f (Swensen.Unquote.Operators.evalRaw x)) s

    let copyTerm u v : Goal =
        let rec buildSubst u s : Subst=
            match u with
            | LVar (Find s _) -> s
            | LVar u -> Map.add u (upcast fresh()) s
            | Patterns.NewUnionCase (_, exprs)
            | Patterns.NewTuple exprs -> 
                List.fold (fun s expr -> buildSubst expr s) s exprs
            | _ -> s
        Goal <| fun s ->
            let u = walkMany u s
            Goal.Subst (equiv_ (walkMany u (buildSubst u Map.empty)) v) s

    