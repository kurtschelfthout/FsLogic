module MiniKanren.Substitution

open System
open System.Collections
open System.Collections.Generic
open System.Threading

///Set this to true to check after 
///unifying whether adding any new substitutions
///would introduce a circularity. This is
///an expensive check so is turned off by
///default.
let mutable occursCheck = false

type VarId = int

let nextId = 
    let varcount = ref 0
    fun () -> Interlocked.Increment(varcount) : VarId

[<CustomEquality; NoComparison>]
type Uni = 
    | LVar of VarId
    | Ctor of (list<Uni> -> obj option) * int * list<Uni>
    | Prim of obj with
    override t.Equals(other) =
        match other with
        | :? Uni as other ->
            match (t,other) with
            | (LVar i, LVar j) -> i = j
            | (Ctor (_, p1, i1), Ctor (_, p2,i2)) -> p1 = p2 && i1 = i2
            | (Prim o1, Prim o2) -> o1 = o2
            | _ -> false
        | _ -> false


let newVar() = LVar <| nextId()

type Subst = Map<VarId,Uni>

let extNoCheck : _ -> _ -> Subst -> Subst = Map.add

let (|Find|_|) map key = Map.tryFind key map

let rec walk v (s:Subst) =
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
    | Ctor (_,_,fields) -> Seq.exists (fun exp -> occurs id exp s) fields
    | Prim _ -> false

///Calls extNoCheck only if the occurs call succeeds.
let ext x v s =
    if occursCheck && occurs x v s then 
        None
    else 
        Some <| extNoCheck x v s

///Unifies two terms u and v with respect to the substitution s, returning
///Some s', a potentially extended substitution if unification succeeds, and None if
///unification fails or would introduce a circularity.
let rec unify u v s = 
    let unifySubExprs exprs1 exprs2 =
        Seq.zip exprs1 exprs2
        |> Seq.fold (fun subst (e1,e2) -> subst |> Option.bind (unify e1 e2)) (Some s)
    let u = walk u s //remember: if u/v is an LVar it will return what it's associated with
    let v = walk v s //otherwise, it will just return  u/v itself
    match (u,v) with
    | LVar u, LVar v when u = v -> Some s
    | LVar u, LVar _ -> Some (extNoCheck u v s) //distinct, unassociated vars never introduce a circularity. Hence extNoCheck.
    | LVar u, _ -> ext u v s
    | _, LVar v -> ext v u s
    | Prim u, Prim v when u = v -> Some s
    | Ctor (_,i,ufields), Ctor (_,j,vfields) when i = j ->  unifySubExprs ufields vfields
    | _ -> None

///Like walk, but also replaces any variables that are bound in the substitution deep
///in the given v.
let rec walkMany v s =
    let v = walk v s
    match v with
    | Ctor (f,i,exprs) -> exprs |> List.map (fun e -> walkMany e s) |> (fun es -> Ctor(f,i,es))
    | _ -> v

let reify v s =
    //Renumber all remaining variables in an expression with names in increasing order.
    let rec reifyS v s =
        let v = walk v s
        match v with
        | LVar v' -> extNoCheck s.Count v s
        | Ctor (_,i,fields) -> fields |> List.fold (fun s field -> reifyS field s) s
        | _ -> s
    let v = walkMany v s
    walkMany v (reifyS v Map.empty)




