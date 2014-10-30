module MiniKanren.Substitution

open System
open System.Collections
open System.Collections.Generic
open System.Threading
open Microsoft.FSharp.Quotations

///Set this to true to check after 
///unifying whether adding any new substitutions
///would introduce a circularity. This is
///an expensive check so is turned off by
///default.
let mutable occursCheck = false

let nextId = 
    let varcount = ref 0
    fun () -> Interlocked.Increment(varcount) 

type LVar<'a> = Expr<'a>

let fresh<'a>() : LVar<'a> = Expr.Var (Var(sprintf "_%i" (nextId()),typeof<'a>) ) |> Expr.Cast
let fresh2() = (fresh(),fresh())
let fresh3() = (fresh(),fresh(),fresh())
let fresh4() = (fresh(),fresh(),fresh(),fresh())

//shortcut to say "don't care"
let __() = fresh()

type Subst = Map<string,Expr>

let extNoCheck = Map.add

let (|LVar|_|) expr = 
    match expr with
    | Patterns.Var v -> Some v.Name
    | _ -> None

let (|Find|_|) map key = Map.tryFind key map

let rec walk v s =
    match v with
    | LVar (Find s rhs) -> walk rhs s 
    | _ -> v

///Returns true if adding an association between x and v
///would introduce a circularity.
///A circularity would in the first instance cause walk to diverge
///(loop infinitely)
let rec occurs id v s =
    let vs = walk v s
    match vs with
    | LVar id' -> id'.Equals(id)
    | Patterns.NewUnionCase (_, exprs)
    | Patterns.NewTuple exprs -> 
        Seq.exists (fun exp -> occurs id exp s) exprs 
    | _ -> false   

///Calls extNoCheck only if the occurs call succeeds.
let ext x v s =
    if occursCheck && occurs x v s then 
        None
    else 
        Some <| extNoCheck x v s

///Unifies two terms u and v with respect to the substitution s, returning
///Some s', a potentially extended substitution if unification succeeds, and None if
///unification fails or would introduce a circularity.
let rec unify u v s : Subst option = 
    let unifySubExprs exprs1 exprs2 =
        Seq.zip exprs1 exprs2
        |> Seq.fold (fun subst (e1,e2) -> subst |> Option.bind (unify e1 e2)) (Some s)
    let u = walk u s //remember: if u/v is a LVar it will return what it's associated with
    let v = walk v s //otherwise, it will just return  u/v itself
    match (u,v) with
    | Patterns.Value (u,_),Patterns.Value (v,_) when u = v -> Some s
    | LVar u, LVar v when u = v-> Some s
    | LVar u, LVar _ -> Some (extNoCheck u v s) //distinct, unassociated vars never introduce a circularity. Hence extNoCheck.
    | LVar u, _ -> ext u v s
    | _, LVar v -> ext v u s
    | Patterns.NewUnionCase (unionCaseInfo1, exprs1), Patterns.NewUnionCase (unionCaseInfo2, exprs2)
        when unionCaseInfo1 = unionCaseInfo2 ->
            unifySubExprs exprs1 exprs2
    | Patterns.NewTuple exprs1,Patterns.NewTuple exprs2
        when exprs1.Length = exprs2.Length && exprs1 |> List.map (fun e -> e.Type) = (exprs2 |> List.map (fun e -> e.Type)) ->
            unifySubExprs exprs1 exprs2
    | _ -> None

///Like walk, but also looks into recursive data structures
let rec walkMany v s =
    let v = walk v s
    match v with
    | Patterns.NewUnionCase (unionCaseInfo, exprs) ->
        Expr.NewUnionCase (unionCaseInfo, exprs |> List.map (fun e -> walkMany e s))
    | Patterns.NewTuple exprs-> 
        Expr.NewTuple (exprs |> List.map (fun e -> walkMany e s))
    | _ -> v
  
//replaces all variables in an expression with names like _0, _1 etc.
let rec reifyS (v:Var) (m:Map<_,_>) =
    match v with
    | Find m v -> m,v
    | _ ->
        let reifyName = sprintf "_%i"
        let reified = Expr.Var (Var(reifyName m.Count,v.Type))
        m |> Map.add v reified,reified

let reify v s =
    let v = walkMany v s
    let map = ref Map.empty
    v.Substitute(fun var -> let (newmap,newvar) = reifyS var !map in map := newmap; Some newvar)



