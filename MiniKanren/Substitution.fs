module MiniKanren.Substitution

open System
open System.Collections
open System.Collections.Generic
open System.Threading

let varcount = ref 0

type Var(?name) = 
    let name = defaultArg name "anon"
    let counter = Interlocked.Increment(varcount)
    override x.ToString() =
        sprintf "%s_%i" name counter

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




