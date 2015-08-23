namespace MiniKanren

module Goal =

    open MiniKanren.Substitution
    open MiniKanren
    open System
    open Microsoft.FSharp.Quotations
    open System.Reflection

    ///A goal is a function that maps a substitution to an
    ///ordered sequence of zero or more values.
    type Goal = Goal of (Subst -> Stream<Subst>) with 
        static member Subst(Goal g) = g
        static member (&&&)(Goal g1,Goal g2) =
            Goal (g1 >=> g2)
        static member (|||)(Goal g1,Goal g2) =
            Goal <| fun s -> g1 s +++ g2 s

    let (|Goals|) (g:list<_>) = g |> List.map Goal.Subst

    let fail = Goal (fun _ -> Stream.mzero)
    let succeed = Goal Stream.unit 

    //this is in two parts because the public operator *=* needs
    //to take Expr<'a> for type inference. But really it can take
    //any Expr, not just the one with a generic type, and this is used
    //further down.

    let private equivImpl u v : Goal =
        Goal <| fun a -> 
            unify u v a
            |> Option.map Stream.unit
            |> Option.defaultTo Stream.mzero

    type Term<'a> = { Uni : Uni } with
        static member ( *=* )( { Uni = u }:Term<'a>, { Uni = v }:Term<'a>) = equivImpl u v

    
    let private newVarTerm<'a> : unit -> Term<'a> = 
        let none = fun _ -> None
        fun () -> { Uni = Substitution.newVar() }
         
//    let inline fresh2() = fresh(),fresh()
//    let inline fresh3() = fresh(),fresh(),fresh()

    

    let private nilProj typex = 
        let emptyMethod = typedefof<_ list>.MakeGenericType([|typex|]).GetMethod("get_Empty")
        let nil = Some <| emptyMethod.Invoke(null, [||])
        fun _ -> nil
    [<GeneralizableValue>]
    let nil<'a> : Term<'a list> = { Uni = Ctor (nilProj typeof<'a>,0,[]) }

    let private tryProject = function
        | (LVar _) -> None
        | (Ctor (p,_,args)) -> p args
        | Prim o -> Some o

    let private consProj typex = 
        let consMethod = typedefof<_ list>.MakeGenericType([|typex|]).GetMethod("Cons")
        let cons x xs = consMethod.Invoke(null, [|x;xs|])
        fun uni ->
            match uni with 
            | [x;xs] -> 
                tryProject x
                |> Option.bind (fun x -> tryProject xs |> Option.map (fun xs -> cons x xs))
            | _ -> None
    let cons (x:Term<'a>) (xs:Term<'a list>) : Term<'a list> = 
        { Uni = Ctor (consProj typeof<'a>, 1, [x.Uni; xs.Uni]) }
       
    let private tupProj (typedef:Type) types =
        let ctorMethod = typedef.MakeGenericType(types).GetConstructor(types)
        let create xs = ctorMethod.Invoke(xs)
        fun uni ->
            let projunis = uni |> List.map tryProject
            match projunis with
            | xs when xs |> List.forall Option.isSome -> 
                xs |> Seq.map Option.get |> Seq.toArray |> create |> Some
            | _ -> 
                None

    let ofList xs = List.foldBack (fun e st -> cons e st) xs nil

    let prim (i:'a) : Term<'a> = { Uni = Prim i }
//    let inline (~~) i  = prim i

    type Unifiable = Unifiable with
        static member inline Unify(a:Term<_>, a') =
            a *=* a'
        static member inline Unify((a:Term<_>,b:Term<_>), (a',b')) =
            a *=* a' &&& b *=* b'
        static member inline Unify((a:Term<_>,b:Term<_>,c:Term<_>), (a',b',c')) =
            a *=* a' &&& b *=* b' &&& c *=* c'
        //Trick: if we want to add another overload, say bool and bool,
        //we need to add at least a second one - otherwise the compiler
        //will not generalize the types. E.g. the below dummy one will do.
        //static member Unify(Unifiable, Unifiable) = succeed

        static member Create(b:bool) = prim b
        static member Create(b:int) = prim b
        static member Create(b:string) = prim b
        static member Create(xs:list<int>) = xs |> List.map prim |> ofList
        static member Create(xs:list<bool>) = xs |> List.map prim |> ofList
        static member Create(xs:list<Term<'a>>) = ofList xs
        static member Create((a:Term<'a>,b:Term<'b>)) = 
            { Uni = Ctor (tupProj typedefof<_ * _> [|typeof<'a>;typeof<'b>|], 2, [a.Uni;b.Uni])}
        static member Create((a:Term<'a>,b:Term<'b>,c:Term<'c>)) = 
            { Uni = Ctor (tupProj typedefof<_*_*_> [|typeof<'a>;typeof<'b>;typeof<'c>|], 3, [a.Uni;b.Uni;c.Uni])}
        static member Create((a:Term<'a>,b:Term<'b>,c:Term<'c>,d:Term<'d>)) = 
            { Uni = Ctor (tupProj typedefof<_*_*_*_> [|typeof<'a>;typeof<'b>;typeof<'c>;typeof<'d>|], 4, [a.Uni;b.Uni;c.Uni;d.Uni])}

        static member Fresh(_:Term<'a>) = 
            newVarTerm<'a>()
        static member Fresh((_:Term<'a>,_:Term<'b>)) = 
            (newVarTerm<'a>(),newVarTerm<'b>())
        static member Fresh((_:Term<'a>,_:Term<'b>,_:Term<'c>)) = 
            (newVarTerm<'a>(),newVarTerm<'b>(),newVarTerm<'c>())
        static member Fresh((_:Term<'a>,_:Term<'b>,_:Term<'c>,_:Term<'d>)) = 
            (newVarTerm<'a>(),newVarTerm<'b>(),newVarTerm<'c>(),newVarTerm<'d>())

    let inline (~~) i : Term<'r> =
        let inline call (t:^t) (a:^a) (r:^b) =
             ((^t or ^a):(static member Create: ^a -> ^b)(a))
        call Unifiable i Unchecked.defaultof<Term<'r>>

    let inline equiv u v =
        let inline call (t:^t) (a:^a) (b:^a) =
             ((^t or ^a):(static member Unify: ^a * ^a -> Goal)(a,b))
        call Unifiable u v

    let inline ( *=* ) a b : Goal =  equiv a b

    let inline fresh() : 'r =  
        let inline call (t:^t) (a:^a) =
             ((^t or ^a):(static member Fresh: ^a -> ^a)(a))
        call Unifiable Unchecked.defaultof<'r>
//    let inline fresh2() = fresh(),fresh()
//    let inline fresh3() = fresh(),fresh(),fresh()

    //shortcut to say "don't care"
    let __<'a> : Term<'a> = fresh()

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

//    let rec takeSeq f =
//        seq { match f with
//              | MZero -> ()
//              | Inc (Lazy s) -> yield! takeSeq s
//              | Unit a -> yield a
//              | Choice(a,f) ->  yield a; yield! takeSeq f
//            }

    let run n (f: Term<'a> -> Goal) =
        Stream.delay (fun () -> 
            let x = fresh()
            let result = Goal.Subst (f x) Map.empty
            result >>= (reify x.Uni >> Stream.unit))
        |> take n
        |> List.map tryProject
        |> List.map (Option.map (fun a -> unbox<'a> a))
//        |> (if n>0 then Seq.take n else (fun x -> x))
//        |> Seq.toList

    //impure operators
    let project ({ Uni = v } as tv:Term<'a>) (f:'a -> Goal) : Goal =
        Goal <| fun s -> 
            //assume atom here..otherwise fail...
            match walkMany v s |> tryProject with
            | Some x -> Goal.Subst (f (unbox x)) s
            | None -> failwithf "project: value is not of type %s" typeof<'a>.Name

    let copyTerm u v : Goal =
        let rec buildSubst s u : Subst =
            match u with
            | LVar (Find s _) -> s
            | LVar u -> Map.add u (newVar()) s
            | Ctor (_, _, exprs) -> List.fold buildSubst s exprs
            | _ -> s
        Goal <| fun s ->
            let u = walkMany u s
            Goal.Subst (equivImpl (walkMany u (buildSubst Map.empty u)) v) s
    
