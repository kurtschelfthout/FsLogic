module MiniKanren

open System
open System.Collections
open System.Collections.Generic

let varcount = ref 0

type Var(?name) = 
    let name = defaultArg name "anon"
    let counter = 
        varcount := !varcount + 1
        !varcount - 1
    override x.ToString() =
        sprintf "%s_%i" name counter

let uncurry f = fun a b -> f (a,b)

type Term = 
    | Nil //just used in List...?
    | Var of Var
    | Atom of obj
    | List of Term * Term
    with
    static member FromSeq(terms:seq<Term>) =
        terms |> Seq.fold (uncurry List) Nil
    static member FromSeq(terms:seq<obj>) =
        terms |> Seq.fold (fun s e -> List(s, Atom e)) Nil
    override this.ToString() =
        match this with
        | Nil -> String.Empty
        | Var v -> v.ToString() //neither of these actually occur in practice, except in debugging
        | Atom o -> o.ToString()
        | List (u1,u2) -> sprintf "%O, %O" u1 u2
        

type Subst = Subst of list<Var*Term> with
    member s.Length =
        match s with (Subst l) -> l.Length
    static member Empty = Subst []

let extNoCheck x v (Subst l) =
    Subst ((x,v) :: l)

let rec walk (v:Term) (Subst s as ss) =
   // printfn "%A %A" v s
   // Console.ReadKey()
    match v with
    | Var v' -> 
        let a = Seq.tryFind (fst >> (=) v') s
        match a with
        | Some (_,rhs) -> walk rhs ss
        | None -> v //if not a variable or not found, return v 
    //this goes into walkmany?
//    | List (v1,v2) -> 
//        let v1r = walk v1 ss
//        let v2r = walk v2 ss
//        List (v1r,v2r)  
    | _ -> v         //this is the recursive base case

///Returns true if adding an association between x and v
///would introduce a circularity.
///A circularity would in the first instance cause walk to diverge
///(loop infinitely)
and occurs (x:Var) v s =
    let vs = walk v s
    match vs with
    | Var v' -> v'.Equals(x)
    | List (t1,t2)-> 
        occurs x t1 s
        || occurs x t2 s
    | _ -> false    

///Calls extNoCheck only if the occurs call succeeds.
let ext x v s =
    if occurs x v s then 
        None
    else 
        Some <| extNoCheck x v s


///Unifies two terms u and v with respect to the substitution s, returning
///Some s', a potentially extended substitution if unification succeeds, and None if
///unification fails or would introduce a circularity.
let rec unify u v s = 
    let u = walk u s //remember: if u/v is a Var it will return what it's associated with
    let v = walk v s //otherwise, it will just return  u/v itself
    match (u,v) with
    | _ when u = v -> Some s
    | Var u, Var _ -> Some (extNoCheck u v s) //distinct, unassociated vars never introduce a circularity. Hence extNoCheck.
    | Var u, _ -> ext u v s
    | _, Var v -> ext v u s
    | List (u1,u2), List (v1,v2) ->
        unify u1 v1 s
        |> Option.bind (unify u2 v2)
    | _ -> None

let rec unifyNoCheck u v s = 
    let u = walk u s
    let v = walk v s
    match (u,v) with
    | _ when u = v -> Some s
    | Var u, _ -> Some <| extNoCheck u v s
    | _, Var v -> Some <| extNoCheck v u s
    | List (u1,u2), List (v1,v2) ->
        unifyNoCheck u1 v1 s
        |> Option.bind (unifyNoCheck u2 v2)
    | _ -> None

///Like walk, but also looks into sequences
let rec walkMany v s =
    let v = walk v s
    match v with
    //| Var _ -> v
    | List (v1,v2) -> List (walkMany v1 s,walkMany v2 s)
    | _ -> v
             
///Extends a substitution s with values for v that are strings _0, _1 etc.
let rec reifyS v s =
    let reifyName = sprintf "_%i"
    let v = walk v s
    match v with
    | Var v -> 
        ext v (Atom <| upcast reifyName s.Length) s 
        |> Option.get //well, it's supposed to throw
    | List (v1,v2) ->
        reifyS v1 s 
        |> reifyS v2
    | _ -> s
    
///Remove al vars from a value given a substitution, if they are unassociated
/// string like _0, _1 are shown
///Note: in a typed setting, this would not return a Subs type, I think, but
///a reified Subst type which looks very similar, but has no Var case.
let reify v s =
    let v = walkMany v s
    walkMany v (reifyS v Subst.Empty)

type Stream<'a> =
    | MZero
    | Unit of 'a
    | Choice of 'a * Stream<'a>
    | Inc of Lazy<Stream<'a>>

module Option =
    let defaultTo a opt =
        match opt with
        | None -> a
        | Some a -> a

//note: minikanren says: A goal is a function maps a substitution to an
//ordered sequence of zero or more values. These are _almost always_ substituions.
type Goal<'a> = Subst -> Stream<'a>

let equiv u v : Goal<_> =
    fun a -> 
        unify u v a
        |> Option.map Unit
        |> Option.defaultTo MZero

let equivNoCheck u v : Goal<_> =
    fun a -> 
        unifyNoCheck u v a
        |> Option.map Unit
        |> Option.defaultTo MZero

let rec mplus a b =
    match a with
    | MZero -> b
    | Unit a -> Choice (a,b)
    | Choice(a,b') -> Choice (a,mplus b b') //interesting - interleaving of the results here
    | Inc a' -> Inc (lazy mplus b a'.Value) 

let rec bind s g =
    match s with
    | MZero -> MZero
    | Unit a -> g a
    | Choice (a,b) -> mplus (g a) (bind b g)
    | Inc f -> Inc (lazy bind f.Value g)

let rec mplusMany streams =
    match streams with
    | [] -> MZero
    | [g] -> g
    | (g::gs) -> mplus g (mplusMany gs)

let rec bindMany str goals =
    match goals with
    | [] -> str
    | (g::gs) -> bindMany (bind str g) gs

let conde (goals:#seq<Goal<_> * #seq<Goal<_>>>) : Goal<_> =
    fun a -> 
        Inc (lazy (mplusMany (goals |> Seq.map (fun (g,gs) -> (bindMany (g a) gs)) |> Seq.toList) ))

let exist x f =
    fun a ->
        Inc (lazy (let (g0::gs)  = f (x |> List.map Var)
                   bindMany (g0 a) gs))

let rec take n f =
    if n = 0 then 
        []
    else
        match f with
        | MZero -> []
        | Inc (Lazy s) -> take n s
        | Unit a -> [a]
        | Choice(a,f) ->  a :: take (n-1) f

let run n f =
    //let's hack this in
    Inc (lazy (let x = Var <| new Var() //"_goal_"
               let (g0::gs)  = f x
               bind (bindMany (g0 Subst.Empty) gs) (Unit << reify x)))
    |> take n

//this doesn't work because the x passed into the reify is not the real var - that is only
//given by exist. And we can't bind the reify inside the exist because then the types don't match.
//Sucks.
//    let g = bind ((exist [x] (fun x -> f x)) Subst.Empty) (reify x >> Unit)
//    take n g

//tests
let bla = run 5 (fun myvar -> [exist [new Var()] (fun [x] -> [equiv x (Atom 3); equiv myvar x])])

let g = run 5 (fun x -> [equiv x (Atom 1)])

let g2 = run 5 (fun q -> [exist [new Var();new Var();new Var()] 
                                (fun [x;y;z]-> [conde [equiv (Term.FromSeq [x; y; z; x]) q,[] 
                                                       equiv (Term.FromSeq [z; y; x; z]) q,[]]])])

let g4 = run 5 (fun q -> [exist [new Var();new Var();new Var()] 
                                (fun [x;y;z]-> [conde [(equiv (List (x, y)) q),[] 
                                                       (equiv (List (y, y)) q),[]]])])

let g3 = run 1(fun q-> [exist [new Var(); new Var()] (fun [x;y] -> [equiv y q; equiv (Atom 3) y])])

let infinite = run 9 (fun q ->  
                let rec loop() =
                    conde <|
                        seq { yield equiv (Atom false) q,[]
                              yield equiv (Atom true) q, []
                              yield loop(),[] }
                [loop()])

///anyo tries g an unbounded number of times
let rec anyo g =
    conde <| seq { yield g,[]; yield anyo g,[] }

let anyTest = run 5 (fun q -> [conde [anyo (equiv (Atom false) q),[]
                                      equiv (Atom true) q,[]]])

let anyTest2 =  
    run 5 (fun q -> 
        [anyo (conde [equiv (Atom 1) q,[]
                      equiv (Atom 2) q,[]
                      equiv (Atom 3) q,[]])])
                
let alwayso = anyo (equiv Nil Nil)

let alwaysoTest =
    run 15 (fun x ->
        [conde [equiv (Atom true) x,[]; equiv (Atom false) x,[]]
         alwayso
         equiv (Atom false) x])

let alwaysoTest2 =
    run 3 (fun q ->
        let nevero = anyo (equiv (Atom true) (Atom false))
        [conde [equiv (Atom 1) q,[]
                nevero,[]
                conde [equiv (Atom 2) q,[]
                       nevero,[]
                       equiv (Atom 3) q,[]],[]]]) 

let rec appendo(l:Term) (s:Term) (out:Term) =
    //printfn "%O %O %O" l s out
    //Console.ReadKey()
    conde [equiv Nil l,[equiv s out]
           exist [new Var("a");new Var("d")] (fun [a; d] ->
            [equiv (List (a,d)) l
             exist [new Var("res")] (fun [res] -> 
                [appendo d s res
                 equiv (List (a,res)) out])]),[]
           ]
            
let appendoTest =
    run 1 (fun q -> [appendo q (List (Atom 5, List(Atom 4,Nil))) (List (Atom 3, List (Atom 5, List(Atom 4, Nil)))) ])

let appendoTest2 =
    run 3 (fun q -> [exist [new Var("l"); new Var("s")] (fun [l;s] -> 
        [appendo l s (List (Atom 1, List(Atom 2,Nil)))
         equiv (List (l,s)) q])])


[<EntryPoint>]
let main args =
    printfn "%O" bla
    printfn "%O" g
    printfn "%O" g2
    printfn "%O" g3
    printfn "%O" g4
    printfn "%O" infinite
    printfn "%O" anyTest
    printfn "%O" anyTest2
    printfn "%O" alwaysoTest
    printfn "%O" alwaysoTest2
    printfn "%A" appendoTest
    printfn "%A" appendoTest2
    //let r = anyTest2()
    //printfn "%A" r
    Console.ReadKey() |> ignore
    0
