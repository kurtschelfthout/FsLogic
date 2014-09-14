module MiniKanren.Substitution

open System
open System.Collections
open System.Collections.Generic
open System.Threading
open Microsoft.FSharp.Quotations

type Id() = 
    static let varcount = ref 0
    let counter = Interlocked.Increment(varcount)
    override __.ToString() = sprintf "_%i" counter
    //can use reference equality and hashcode  

type LVar<'a> = Expr<'a>

let fresh<'a>() : LVar<'a> = Expr.Var (Var(Id().ToString(),typeof<'a>) ) |> Expr.Cast

type Subst = Subst of list<int*Expr> with
    member s.Length =
        match s with (Subst l) -> l.Length
    static member Empty = Subst []

let extNoCheck x v (Subst l) =
    Subst ((x,v) :: l)

let (|LVar|_|) expr = 
    match expr with
    | Patterns.Var v ->
        //this is annoying - name can only be a string, so we need to convert to and from each time.
        Some <| Int32.Parse(v.Name.Remove(0,1))
    | _ -> None

let rec walk (v:#Expr) (Subst s as ss)  =
    match v with
    | LVar id -> 
        let a = Seq.tryFind (fst >> (=) id) s
        match a with
        | Some (_,rhs) -> walk (rhs :?> 'a) ss
        | None -> v //if not a variable or not found, return v 
    | _ -> v

///Returns true if adding an association between x and v
///would introduce a circularity.
///A circularity would in the first instance cause walk to diverge
///(loop infinitely)
let rec occurs id v s =
    let vs = walk v s
    match vs with
    | LVar id' -> id'.Equals(id)
    | Patterns.NewUnionCase (unionCaseInfo, exprs) ->
        Seq.exists (fun exp -> occurs id exp s) exprs        
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
    | Patterns.Value (u,_),Patterns.Value (v,_) when u = v -> Some s
    | LVar u, LVar v when u = v -> Some s
    | LVar u, LVar _ -> Some (extNoCheck u v s) //distinct, unassociated vars never introduce a circularity. Hence extNoCheck.
    | LVar u, _ -> ext u v s
    | _, LVar v -> ext v u s
    | Patterns.NewUnionCase (unionCaseInfo1, exprs1), Patterns.NewUnionCase (unionCaseInfo2, exprs2)
        when unionCaseInfo1 = unionCaseInfo2 ->
        exprs1
        |> Seq.zip exprs2
        |> Seq.fold (fun subst (e1,e2) -> subst |> Option.bind (unify e1 e2)) (Some s)
    | _ -> None

//let rec unifyNoCheck u v s = 
//    let u = walk u s
//    let v = walk v s
//    match (u,v) with
//    | Patterns.Value (u,_),Patterns.Value (v,_) when u = v -> Some s
//    | LVar u, LVar v when u = v -> Some s
//    | LVar u, LVar _ -> Some (extNoCheck u v s) //distinct, unassociated vars never introduce a circularity. Hence extNoCheck.
//    | LVar u, _ -> Some (extNoCheck u v s)
//    | _, LVar v -> Some (extNoCheck v u s)
//    | Patterns.NewUnionCase (unionCaseInfo1, exprs1), Patterns.NewUnionCase (unionCaseInfo2, exprs2)
//        when unionCaseInfo1 = unionCaseInfo2 ->
//        exprs1
//        |> Seq.zip exprs2
//        |> Seq.fold (fun subst (e1,e2) -> subst |> Option.bind (unify e1 e2)) (Some s)
//    | _ -> None

///Like walk, but also looks into recursive data structures
let rec walkMany v s =
    let v = walk v s
    match v with
    | Patterns.NewUnionCase (unionCaseInfo, exprs) -> 
        Expr.NewUnionCase (unionCaseInfo, exprs |> List.map (fun e -> walkMany e s))
    | _ -> v
  
//type Reified =
//    | Var of int //unknown value, _0
//    | Value of string //ToString of known value 
//    with
//    interface IUnify with //fake implementation, never used.
//        member this.Var = None
//        member this.Occurs(_,_,_) = false
//        member this.Unify(other,s) = None
//        member this.Walk(s) = this :> IUnify
//        member this.Reify(s) = s
//
/////Extends a substitution s with values for v that are strings _0, _1 etc.
//let rec reifyS v s =
//    let reifyName = sprintf "_%i"
//    let v = walk v s
//    match v.Var with
//    | Some v -> 
//        ext v (Value <| reifyName s.Length) s 
//        |> Option.get //well, it's supposed to throw
////    | List (v1,v2) ->
////        reifyS v1 s 
////        |> reifyS v2
//    | _ -> v.Reify(s)
//
/////Remove al vars from a value given a substitution, if they are unassociated
/////strings like _0, _1 are shown
/////Note: in a typed setting, this would not return a Subs type, I think, but
/////a reified Subst type which looks very similar, but has no Var case.
//let reify v s =
//    let v = walkMany v s
//    walkMany v (reifyS v Subst.Empty)




