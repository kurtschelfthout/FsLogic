namespace FsLogic

module Goal =

    open Substitution
    open System
    open System.Reflection

    /// A goal is a function that maps a constraint package to an
    /// stream of packages.
    type Goal = Goal of (Package -> Stream<Package>) with 
        static member Subst(Goal g) = g
        static member (&&&)(Goal g1, Goal g2) =
            Goal (g1 >=> g2)
        static member (|||)(Goal g1, Goal g2) =
            Goal (fun s -> g1 s +++ g2 s)

    let (|Goals|) (g:list<_>) = g |> List.map Goal.Subst

    let fail = Goal (fun _ -> Stream.mzero)
    let succeed = Goal Stream.unit 

    let private unifyImpl u v : Goal =
        let unifyExtAll c =
            let lhs l = List.map (fst >> Var) l
            let rhs l = List.map snd l
            unifySubExprs (lhs c) (rhs c)

        // Simplify the disequality constraints by unifying their left and right hand sides
        // in the given substitution.
        let rec verifyConstraints store accNewStore subst =
            match store with
            | [] -> Some accNewStore
            | c::cs ->
                match unifyExtAll c subst with
                //if a constraint doesn't unify in the current substitution, so it can never be equal. It can thus be removed.
                | None -> verifyConstraints cs accNewStore subst
                //a constraint unifies without extending the substitution. In other words the constraint is violated.
                | Some (_,[]) -> None
                //a constraint unifies with extending the substitution. The extension is a simplified constraint that we must track,
                //so we add it to the constraint store.
                | Some (s',ext) -> verifyConstraints cs (ext::accNewStore) subst

        Goal <| fun p -> 
            match unify u v p.Substitution with
            | None -> Stream.mzero
            | Some s when obj.ReferenceEquals(p.Substitution,s) -> Stream.unit p
            | Some s ->
                match verifyConstraints p.ConstraintStore [] s with
                | Some c -> Stream.unit { Substitution = s; ConstraintStore = c}
                | None -> Stream.mzero
            
    let private disunifyImpl u v : Goal =
        Goal <| fun p ->
            match unifyExt u v p.Substitution with
            | None -> Stream.unit p
            | Some (_,[]) -> Stream.mzero
            | Some (s,ext) -> Stream.unit { p with ConstraintStore = ext :: p.ConstraintStore}
    
    type Term<'a> = { Uni : Term } with
        static member ( *=* ) ( { Uni = u }:Term<'a>, { Uni = v }: Term<'a>) = unifyImpl u v
        static member ( *<>* )( { Uni = u }:Term<'a>, { Uni = v }: Term<'a>) = disunifyImpl u v
    
    let private newVarTerm<'a>() : Term<'a> = { Uni = Substitution.newVar() }
         
    let private nilProj typex = 
        let emptyMethod = typedefof<_ list>.MakeGenericType([|typex|]).GetMethod("get_Empty")
        let nil = Some <| emptyMethod.Invoke(null, [||])
        fun _ -> nil

    [<GeneralizableValue>]
    let nil<'a> : Term<'a list> = { Uni = Ctor (nilProj typeof<'a>,0,[]) }

    let private tryProject = function
        | (Var _) -> None
        | (Ctor (p,_,args)) -> p args
        | Atom o -> Some o

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

    let prim (i:'a) : Term<'a> = { Uni = Atom i }

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

        static member Create(b:int) = prim b
        static member Create(b:bool) = prim b
        static member Create(b:string) = prim b

        static member Create(xs:list<int>) = xs |> List.map prim |> ofList
        static member Create(xs:list<bool>) = xs |> List.map prim |> ofList
        static member Create(xs:list<string>) = xs |> List.map prim |> ofList
        static member Create(xs:list<Term<'a>>) = ofList xs

        static member Create((a:Term<'a>,b:Term<'b>)) = 
            { Uni = Ctor (tupProj typedefof<_ * _> [|typeof<'a>;typeof<'b>|], 2, [a.Uni;b.Uni])}
        static member Create((a:Term<'a>,b:Term<'b>,c:Term<'c>)) = 
            { Uni = Ctor (tupProj typedefof<_*_*_> [|typeof<'a>;typeof<'b>;typeof<'c>|], 3, [a.Uni;b.Uni;c.Uni])}
        static member Create((a:Term<'a>,b:Term<'b>,c:Term<'c>,d:Term<'d>)) = 
            { Uni = Ctor (tupProj typedefof<_*_*_*_> [|typeof<'a>;typeof<'b>;typeof<'c>;typeof<'d>|], 4, [a.Uni;b.Uni;c.Uni;d.Uni])}
        static member Create((a:Term<'a>,b:Term<'b>,c:Term<'c>,d:Term<'d>,e:Term<'e>)) = 
            { Uni = Ctor (tupProj typedefof<_*_*_*_*_> [|typeof<'a>;typeof<'b>;typeof<'c>;typeof<'d>;typeof<'e>|], 5, [a.Uni;b.Uni;c.Uni;d.Uni;e.Uni])}

        static member Fresh(_:Term<'a>) = 
            newVarTerm<'a>()
        static member Fresh((_:Term<'a>,_:Term<'b>)) = 
            (newVarTerm<'a>(),newVarTerm<'b>())
        static member Fresh((_:Term<'a>,_:Term<'b>,_:Term<'c>)) = 
            (newVarTerm<'a>(),newVarTerm<'b>(),newVarTerm<'c>())
        static member Fresh((_:Term<'a>,_:Term<'b>,_:Term<'c>,_:Term<'d>)) = 
            (newVarTerm<'a>(),newVarTerm<'b>(),newVarTerm<'c>(),newVarTerm<'d>())
        static member Fresh((_:Term<'a>,_:Term<'b>,_:Term<'c>,_:Term<'d>,_:Term<'e>)) = 
            (newVarTerm<'a>(),newVarTerm<'b>(),newVarTerm<'c>(),newVarTerm<'d>(),newVarTerm<'e>())

    let inline (~~) i : Term<'r> =
        let inline call (t:^t) (a:^a) (r:^b) =
             ((^t or ^a):(static member Create: ^a -> ^b)(a))
        call Unifiable i Unchecked.defaultof<Term<'r>>

    let inline ( *=* ) u v = 
        let inline call (t:^t) (a:^a) (b:^a) =
             ((^t or ^a):(static member Unify: ^a * ^a -> Goal)(a,b))
        call Unifiable u v

    let inline fresh() : 'r =  
        let inline call (t:^t) (a:^a) =
             ((^t or ^a):(static member Fresh: ^a -> ^a)(a))
        call Unifiable Unchecked.defaultof<'r>

    //shortcut to say "don't care"
    let __<'a> : Term<'a> = fresh()

    let all (Goals goals) : Goal =
        let g = goals |> List.head
        let gs = goals |> List.tail
        Goal <| fun a -> Stream.delay (fun () -> (Stream.bindMany (g a) gs))

//You would think the following type would make conde better:
//    type Clause<'a> = Clause of 'a * list<'a>
//
//    let inline (<==) head rest = Clause (head, rest)
//
// and this is indeed nice for clauses with a head and a body:
//    conde [ head ==> [ body ]; head2 ==> [ body2 ] ]
// but what about lone facts? Then that needs some extra syntax.
// so it seem altogether not desirable.

    let conde (goals:#seq<list<Goal>>) : Goal =
        let ife a = function
            | [] -> Stream.mzero
            | (Goal g)::(Goals gs) -> Stream.bindMany (g a) gs

        Goal <| fun a -> 
            Stream.delay (fun () -> 
                (Stream.mplusMany (goals |> Seq.map (ife a) |> Seq.toList)))

    ///To be used with matche:
    /// matche (a,b,c) [ pattern ->> [ goals ]; ... ]
    let inline (->>) pat body = (pat,body)

    ///Use kind of like pattern match: just calls equiv with the first argument 
    ///on all the heads of a given list; joining them in a conde.
    let inline matche pat (goals:(_ * Goal list) list) = 
        goals
        |> List.map (fun (h,l) -> (pat *=* h) :: l)
        |> conde

    let conda (goals:list<list<Goal>>) : Goal = 
        let rec ifa subst = function
            | [] | []::_ -> Stream.mzero
            | ((Goal g)::(Goals gs)) :: gss ->
                let rec loop = function
                    | MZero -> ifa subst gss
                    | Inc f -> loop f.Value
                    | Unit _  
                    | Choice (_,_) as a -> Stream.bindMany a gs
                loop (g subst)
        Goal <| fun subst -> ifa subst goals

    let condu (goals:list<list<Goal>>) : Goal = 
        let rec ifu subst = function
            | [] | []::_ -> Stream.mzero
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

    let private runImpl n (f: Term<'a> -> Goal) =
        Stream.delay (fun () -> 
            let x = fresh()
            let result = Goal.Subst (f x) Package.Empty
            result >>= (fun r -> r.Substitution |> reify x.Uni |> Stream.unit))
        |> Stream.toSeq
        |> (if n>0 then Seq.take n else id)

    let runRaw n (f: Term<'a> -> Goal) =
        runImpl  n f
        |> Seq.map (fun t -> { Uni = t } : Term<'a>)
        |> Seq.toList

    let run n (f: Term<'a> -> Goal) =
        runImpl n f
        |> Seq.map tryProject
        |> Seq.map (Option.map unbox<'a>)
        |> Seq.toList

    //impure operators
    let project ({ Uni = v } as tv:Term<'a>) (f:'a -> Goal) : Goal =
        Goal <| fun p -> 
            //assume atom here..otherwise fail...
            match walkMany v p.Substitution |> tryProject with
            | Some x -> Goal.Subst (f (unbox x)) p
            | None -> failwithf "project: value is not of type %s" typeof<'a>.Name

    let copyTerm (u:Term<'a>) (v:Term<'a>) : Goal =
        let rec buildSubst s u : Subst =
            match u with
            | Var (Find s _) -> s
            | Var u -> Map.add u (newVar()) s
            | Ctor (_, _, exprs) -> List.fold buildSubst s exprs
            | _ -> s
        Goal <| fun p ->
            let u = walkMany u.Uni p.Substitution
            Goal.Subst (unifyImpl (walkMany u (buildSubst Map.empty u)) v.Uni) p
    
