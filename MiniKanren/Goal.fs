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

    type Term<'a> = { Uni : Uni
                      Project: Uni -> 'a option
                    } with
        static member ( *=* )( { Uni = u }:Term<'a>, { Uni = v }:Term<'a>) = equivImpl u v
    
    
    
    let fresh : unit -> Term<'a> = 
        let none = fun _ -> None
        fun () -> { Uni = Substitution.newVar(); Project=none }
         
    let inline fresh2() = fresh(),fresh()
    let inline fresh3() = fresh(),fresh(),fresh()

    //shortcut to say "don't care"
    let __<'a> : Term<'a> = fresh()

//    [<GeneralizableValue>]
//    let list<'a> : Term<'a list> * (Term<'a> -> Term<'a list> -> Term<'a list>)  = 
//            datatype (cons0 [] <|> cons2 (curry List.Cons))

    let private nilProj uni = match uni with Ctor (0,[]) -> Some [] | _ -> None
    let nil = { Uni = Ctor (0,[])
                Project = nilProj }

    let private consProj (projectx:Uni -> 'a option) (projectxs:Uni -> option<'a list>) uni = 
        match uni with 
        | Ctor(1, [x;xs]) -> 
            projectx x
            |> Option.bind (fun x -> projectxs xs |> Option.map (fun xs -> (x :: xs)))
        | _ -> None
    let cons (x:Term<'a>) (xs:Term<'a list>) = 
        { Uni = Ctor (1, [x.Uni; xs.Uni])
          Project = consProj x.Project xs.Project}

    let ofList xs = xs |> List.fold (fun st e -> cons e st) nil

    //i is passed in as a convenient way to pass the 'a type, its value is not used.
    let private primProj (i:'a) uni =
        match uni with
        | (Prim (:? 'a as i)) -> Some i
        | _ -> None
    let prim (i:'a) : Term<'a> = { Uni = Prim i
                                   Project = primProj i
                                 }
    let inline (~~) i  = prim i

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

    let inline equiv u v =
        let inline call (t:^t) (a:^a) (b:^b) =
             ((^t or ^a):(static member Unify: ^a * ^a -> Goal)(a,b))
        call Unifiable u v

    let inline ( *=* ) a b : Goal =  equiv a b

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

    let run n (f: _ -> Goal) =
        Stream.delay (fun () -> 
            let x = fresh()
            let result = Goal.Subst (f x) Map.empty
            result >>= (reify x.Uni >> Stream.unit))
        |> take n

    //impure operators
    let project ({ Uni = v } as tv:Term<'a>) (f:'a -> Goal) : Goal =
        Goal <| fun s -> 
            //assume atom here..otherwise fail...
            match walkMany v s |> tv.Project with
            | Some x -> Goal.Subst (f x) s
            | None -> failwithf "project: value is not of type %s" typeof<'a>.Name

    let copyTerm u v : Goal =
        let rec buildSubst s u : Subst =
            match u with
            | LVar (Find s _) -> s
            | LVar u -> Map.add u (newVar()) s
            | Ctor (_, exprs) -> List.fold buildSubst s exprs
            | _ -> s
        Goal <| fun s ->
            let u = walkMany u s
            Goal.Subst (equivImpl (walkMany u (buildSubst Map.empty u)) v) s
    
