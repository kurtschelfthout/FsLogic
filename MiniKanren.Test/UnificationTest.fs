module UnificationTest

open Xunit
open Swensen.Unquote
open MiniKanren.Substitution
open Microsoft.FSharp.Quotations

#nowarn "25"

[<Fact>]
let ``unifying two identical variables should succeed and not extend subst``() =
    let (LVar aName) as a = fresh()
    unify a a Map.empty =? Some Map.empty

[<Fact>]
let ``unifying two different variables should succeed and extend subst``() =
    let (LVar aName) as a = fresh()
    let (LVar bName) as b = fresh()
    let expected = [ (aName, b :> Expr) ] |> Map.ofList
    unify a b Map.empty =? Some expected
    let expected = [ (bName, a :> Expr) ] |> Map.ofList
    unify b a Map.empty =? Some expected

[<Fact>]
let ``unifying variable with value should succeed and extend subst``() =
    let (LVar aName) as a = fresh()
    let expected = [ (aName, <@ 0 @> :> Expr) ] |> Map.ofList
    unify a <@ 0 @> Map.empty =? Some expected
    unify <@ 0 @> a Map.empty =? Some expected

[<Fact>]
let ``unifying different values should fail``() =
    unify <@ 1 @> <@ 0 @> Map.empty =? None
    
[<Fact>]
let ``unifying same values should succeed without extending substitution``() =
    unify <@ 0 @> <@ 0 @> Map.empty =? Some Map.empty

[<Fact>]
let ``unifying head of list with variable should extend substitution``() =
    let (LVar aName) as a = fresh<int>()
    let expected = [ (aName, <@ 0 @> :> Expr) ] |> Map.ofList
    unify <@ [ %a ] @> <@ [ 0 ] @> Map.empty =? Some expected
    unify <@ [ 0 ] @> <@ %a::[] @> Map.empty =? Some expected

[<Fact>]
let ``unifying tail of list with variable should extend substitution``() =
    let (LVar aName) as a = fresh<int list>()
    let expected = [ (aName, <@ [1;2] @> :> Expr) ] |> Map.ofList
    unify <@ 3::%a @> <@ [ 3;1;2 ] @> Map.empty =? Some expected
    unify <@ [ 3;1;2 ] @> <@ 3::%a @> Map.empty =? Some expected

[<Fact>]
let ``unifying element of tuple with variable should extend substitution``() =
    let (LVar aName) as a = fresh<int>()
    let expected = [ (aName, <@ 0 @> :> Expr) ] |> Map.ofList
    unify <@ %a,1 @> <@ 0,1 @> Map.empty =? Some expected
    unify <@ 0,1 @> <@ %a,1 @> Map.empty =? Some expected