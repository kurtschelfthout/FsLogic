module UnificationTest

open Xunit
open Swensen.Unquote
open MiniKanren.Substitution
open Microsoft.FSharp.Quotations

#nowarn "25"

[<Fact>]
let ``unifying two identical variables should succeed and not extend subst``() =
    let a = newVar()
    unify a a Map.empty =? Some Map.empty

[<Fact>]
let ``unifying two different variables should succeed and extend subst``() =
    let (LVar aName) as a = newVar()
    let (LVar bName) as b = newVar()

    let expected = [ (aName, b) ] |> Map.ofList
    unify a b Map.empty =? Some expected

    let expected = [ (bName, a) ] |> Map.ofList
    unify b a Map.empty =? Some expected

let zero = Prim 0
let one = Prim 1

[<Fact>]
let ``unifying variable with value should succeed and extend subst``() =
    let (LVar aName) as a = newVar()

    let expected = [ (aName, zero) ] |> Map.ofList
    unify a zero Map.empty =? Some expected
    unify zero a Map.empty =? Some expected

[<Fact>]
let ``unifying different values should fail``() =
    unify one zero Map.empty =? None
    
[<Fact>]
let ``unifying same values should succeed without extending substitution``() =
    unify zero zero Map.empty =? Some Map.empty

let nil = Ctor ((fun _ -> None),0,[])
let private consProj : Uni list -> obj option = (fun _ -> None)
let cons x xs = Ctor (consProj,1,[x;xs])
let list2 (x,y) = cons x (cons y nil)
[<Fact>]
let ``unifying head of list with variable should extend substitution``() =
    let (LVar aName) as a = newVar()
    let expected = [ (aName, zero ) ] |> Map.ofList
    unify (cons a nil) (cons zero nil) Map.empty =? Some expected
    unify (cons zero nil) (cons a nil) Map.empty =? Some expected

[<Fact>]
let ``unifying tail of list with variable should extend substitution``() =
    let (LVar aName) as a = newVar()
    let expected = [ (aName, list2 (Prim 1,Prim 2)) ] |> Map.ofList
    unify (cons (Prim 3) a) (cons (Prim 3) (list2 (Prim 1, Prim 2))) Map.empty =? Some expected
    unify (cons (Prim 3) (list2 (Prim 1, Prim 2))) (cons (Prim 3) a) Map.empty =? Some expected

[<Fact>]
let ``unifying element of tuple with variable should extend substitution``() =
    let (LVar aName) as a = newVar()
    let expected = [ (aName, zero) ] |> Map.ofList
    unify (list2 (a,Prim 1)) (list2 (Prim 0, Prim 1)) Map.empty =? Some expected
    unify (list2 (Prim 0, Prim 1)) (list2 (a,Prim 1)) Map.empty =? Some expected