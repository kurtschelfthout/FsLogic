module MiniKanren.Substitution

open System
open System.Collections
open System.Collections.Generic
open System.Threading

type Id() = 
    static let varcount = ref 0
    let counter = Interlocked.Increment(varcount)
    override __.ToString() =
        sprintf "var_%i" counter
    //can use reference equality and hashcode

type LVar = Id



    

//type Term = 
//    | Nil //just used in List
//    | Var of Id
//    | Atom of obj
//    | List of Term * Term
//    with
//    static member FromSeq(terms:seq<Term>) =
//        terms |> Seq.fold (curry List) Nil
//    static member FromSeq(terms:seq<obj>) =
//        terms |> Seq.fold (fun s e -> List(s, Atom e)) Nil
//    override this.ToString() =
//        match this with
//        | Nil -> String.Empty
//        | Var v -> v.ToString() //neither of these actually occur in practice, except in debugging
//        | Atom o -> o.ToString()
//        | List (u1,u2) -> sprintf "%O, %O" u1 u2
        

type Subst = Subst of list<Id*IUnify> with
    member s.Length =
        match s with (Subst l) -> l.Length
    static member Empty = Subst []

and IUnify =
    abstract Var : Id option
    abstract Occurs : Id * IUnify * Subst -> bool
    abstract Unify : IUnify * Subst -> Subst option



let inline fresh() = 
    let f = (^a : (static member Fresh : unit -> ^a when ^a :> IUnify) ())
    f

let extNoCheck x v (Subst l) =
    Subst ((x,v) :: l)

let rec walk (v:IUnify) (Subst s as ss) =
   // printfn "%A %A" v s
   // Console.ReadKey()
    match v.Var with
    | Some v' ->
        let a = Seq.tryFind (fst >> (=) v') s
        match a with
        | Some (_,rhs) -> walk rhs ss
        | None -> v //if not a variable or not found, return v 
    | None -> v

///Returns true if adding an association between x and v
///would introduce a circularity.
///A circularity would in the first instance cause walk to diverge
///(loop infinitely)
let rec occurs (x:Id) v s =
    let vs = walk v s
    match vs.Var with
    | Some v' -> v'.Equals(x)
    | None -> vs.Occurs(x, v, s)

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
    match (u.Var,v.Var) with
    | (u,v) when u = v -> Some s
    | Some u, Some _ -> Some (extNoCheck u v s) //distinct, unassociated vars never introduce a circularity. Hence extNoCheck.
    | Some u, _ -> ext u v s
    | _, Some v -> ext v u s
//    | List (u1,u2), List (v1,v2) ->
//        unify u1 v1 s
//        |> Option.bind (unify u2 v2)
    | _ -> u.Unify(v,s)

let rec unifyNoCheck u v s = 
    let u = walk u s
    let v = walk v s
    match (u.Var,v.Var) with
    | (u,v) when u = v -> Some s
    | Some u, _ -> Some <| extNoCheck u v s
    | _, Some v -> Some <| extNoCheck v u s
//    | List (u1,u2), List (v1,v2) ->
//        unifyNoCheck u1 v1 s
//        |> Option.bind (unifyNoCheck u2 v2)
    | _ -> u.Unify(v,s) //should be unify no check, but the "no check" part should be handled differently anyway (maybe release vs debug?)

/////Like walk, but also looks into Lists.
//let rec walkMany v s =
//    let v = walk v s
//    match v with
//    | List (v1,v2) -> List (walkMany v1 s,walkMany v2 s)
//    | _ -> v
//             
/////Extends a substitution s with values for v that are strings _0, _1 etc.
//let rec reifyS v s =
//    let reifyName = sprintf "_%i"
//    let v = walk v s
//    match v with
//    | Var v -> 
//        ext v (Atom <| upcast reifyName s.Length) s 
//        |> Option.get //well, it's supposed to throw
//    | List (v1,v2) ->
//        reifyS v1 s 
//        |> reifyS v2
//    | _ -> s
//    
/////Remove al vars from a value given a substitution, if they are unassociated
/////strings like _0, _1 are shown
/////Note: in a typed setting, this would not return a Subs type, I think, but
/////a reified Subst type which looks very similar, but has no Var case.
//let reify v s =
//    let v = walkMany v s
//    walkMany v (reifyS v Subst.Empty)




