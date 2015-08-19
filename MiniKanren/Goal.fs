namespace MiniKanren

module Goal =

    open MiniKanren.Substitution
    open MiniKanren
    open System
    open Microsoft.FSharp.Quotations

    ///A goal is a function that maps a substitution to an
    ///ordered sequence of zero or more values.
    type Goal = Goal of (Subst -> Stream<Subst>) with 
        static member Subst(Goal g) = g
        static member (&&&)(Goal g1,Goal g2) =
            Goal (g1 >=> g2)
        static member (|||)(Goal g1,Goal g2) =
            Goal <| fun s -> g1 s +++ g2 s

    let (|Goals|) (g:list<_>) = g |> List.map Goal.Subst

    //this is in two parts because the public function equiv needs
    //to take Expr<'a> for type inference. But really it can take
    //any Expr, not just the one with a generic type, and this is used
    //further down.

    let private equivImpl (u:'a) (v:'a) : Goal =
        Goal <| fun a -> 
            unify u v a
            |> Option.map Stream.unit
            |> Option.defaultTo Stream.mzero

    let equiv (u:Expr<'a>) (v:Expr<'a>) : Goal =
        equivImpl u v

//here are some experiments to make the interface to
//unification a bit more palatable. With only the above,
//all the values need to be manually quoted, and together with
//splicing this makes the syntax quite heavy. (see further and tests for
//examples).

//The challenge is to make this work well for all combinations:
// Expr<'a> + Expr<'a>
// 'a + Expr<'a>
// Expr<'a> + 'a

// This uses auto-quotation of method arguments. It works quite
// well, in that it gets rid of all the quotes, but you need to splice
// all variables. And sadly auto-quotation only works for methods, hence the
// corny Uni.fy.
//    type Uni private() =
//        static member fy([<ReflectedDefinition>] u:Expr<'T>,[<ReflectedDefinition>] v:Expr<'T>) =
//            equiv u v

// Interestingly, even writing the constraints down in runtime code is pretty
// hard. I think this is probably too lenient a type. But worth a try.       
//    let (-=-) (u:'a) (v:'b) =
//// need two different types, 'a and 'b if one can be a value.
//        let u',v' = box u,box v
//        match (u',v') with
//// hmm, how to write this?
//        | (:? Expr as u), (:? Expr as v) -> equivImpl u v
//        | (:? Expr as u), _ -> equivImpl u (upcast <@ v @>)
//        | _, (:? Expr as v) -> equivImpl (<@ u @> :> Expr) v
//        | _, _ -> equivImpl (<@ u @> :> Expr) (<@ v @> :> Expr)

// this extension method is relatively ok because you can now write
// x .Equiv 3. or x .Equiv %y. It may be the best compromise. The downside
// is that it makes unification syntactically assymetric. And the fact that
// unification is symmetric is just one of its main selling points.
//    type Microsoft.FSharp.Quotations.Expr<'T> with
//        member x.Equiv([<ReflectedDefinition>]other:Expr<'T>) = equiv x other
//     
// this is to allow writing 3 .Equiv x, but it almost sorta doesnt work with
// the above extension method, though I should experiment more.
//    [<System.Runtime.CompilerServices.Extension>]  
//    type Ext =
//        [<System.Runtime.CompilerServices.Extension>]
//        static member Equiv(x:'T,other:Expr<'T>) = 
//            equiv <@ x @> other

//this trick for unification overloading doesn't
//really work well.
//    type Equiv = Equiv with
//        static member (-=-)(l, v) = 
//            equiv l <@ v @>
//        static member (-=-)(v, r) = 
//            equiv <@ v @> r
//        //static member (?<-)(Equiv, l:Quotations.Expr<'a>,r:Quotations.Expr<'a>) =
        //    equiv l r
 
    //let inline (-=-) l r = Equiv.E(l, r)

// Just some examples to play with things.
//    let examples =
//        let x,y = fresh2()
//        Uni.fy( %x , 3 )
//        &&& Uni.fy( [%x] , %y)
//        &&& Uni.fy( [3;%x] , %y)

        //x -=- y &&& <@ 3 @> -=- y
        //Test.Equiv(6, 3)
        //x.Equiv 3
        //&&& 3.Equiv x
        //&&& x.Equiv y

    let all (Goals goals) : Goal =
        let g = goals |> List.head
        let gs = goals |> List.tail
        Goal <| fun a -> Stream.delay (fun () -> (Stream.bindMany (g a) gs))

//TODO to make conde better:
//    type Clause<'a> = Clause of 'a * list<'a>
//
//    let inline (<==) head rest = Clause (head, rest)

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
                    | Choice (_,_) as a -> Stream.bindMany a g
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
(*
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
            Goal.Subst (equivImpl (walkMany u (buildSubst u Map.empty)) v) s
*)    
