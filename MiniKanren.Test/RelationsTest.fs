
module RelationsTest

open MiniKanren.Goal
open MiniKanren.Substitution
open MiniKanren.Relations
open Xunit
open Swensen.Unquote
open Microsoft.FSharp.Quotations

//from a quotation structured as let...in... get
//the expression after the in. This makes it easier
//to write a quotation that has unbound variables
//which in turn we need to compare the results of some
//tests.
let rec getResult letExpr =
    match letExpr with
    | Patterns.Let (_,_,body) -> getResult body
    | b -> b

[<Fact>]
let g0() = 
    let goal (q:LVar<_>) = 
        let x = fresh() 
        //3 .Equiv x
        equiv x <@ 3 @>
        &&& equiv q x
    let res = runEval -1 goal
    res =? [ 3 ]

[<Fact>]
let g1() = 
    let res = runEval -1 (fun x ->  equiv x <@ 1 @>)
    res =? [ 1 ]

[<Fact>]
let g2() = 
    let res = 
        run -1 (fun q -> 
            let (x,y,z) = fresh(),fresh(),fresh()
            equiv q <@ [%x; %y; %z; %x]  @>
            ||| equiv q <@ [%z; %y; %x; %z] @>)
    2 =? res.Length
    //numbering restarts with each value
    let expected = <@ let _0,_1,_2 =fresh(),fresh(),fresh() in [ _0;_1;_2;_0 ] @> |> getResult
    sprintf "%A" [ expected; expected ] =? sprintf "%A" res

[<Fact>]
let g3() = 
    let res = 
        runEval -1 (fun q -> 
            let y = fresh()
            equiv y q &&& equiv <@ 3 @> y)
    res =? [3]

[<Fact>]
let g4() = 
    let res = 
        run -1 (fun q -> 
            let x,y,z = fresh(),fresh(),fresh()
            equiv <@ [%x; %y] @> q
            ||| equiv <@ [%y; %y] @> q)
    2 =? res.Length
    let expected0 = <@ let _0,_1 =fresh(),fresh() in [ _0;_1 ] @> |> getResult
    let expected1 = <@ let _0 =fresh() in [ _0;_0 ] @> |> getResult
    sprintf "%A" [ expected0; expected1 ] =? sprintf "%A" res

[<Fact>]
let infinite() = 
    let res = runEval 7 (fun q ->  
                let rec loop() =
                    conde [ [ equiv <@ false @> q ]
                            [ equiv q <@ true @> ]
                            [ recurse loop] ]
                loop())
    res =? [ false; true; false; true; false; true; false]


[<Fact>]
let anyoTest() = 
    let res = runEval 5 (fun q -> anyo (equiv <@ false @> q) ||| equiv <@ true @> q)
    res =? [true; false; false; false; false]

[<Fact>]
let anyoTest2() =  
    let res = runEval 5 (fun q -> 
        anyo (equiv <@ 1 @> q
              ||| equiv <@ 2 @> q
              ||| equiv <@ 3 @> q))
    res =? [1; 3; 1; 2; 3]

[<Fact>]
let alwaysoTest() =
    let res = runEval 5 (fun x ->
        (equiv <@ true @> x ||| equiv <@ false @> x)
        &&& alwayso
        &&& equiv <@ false @> x)
    res =? [false; false; false; false; false]

[<Fact>]
let neveroTest() =
    let res = runEval 3 (fun q -> //more than 3 will diverge...
        equiv <@ 1 @> q
        ||| nevero
        ||| equiv <@ 2 @> q
        ||| nevero
        ||| equiv <@ 3 @> q) 
    res =? [1; 3; 2]

[<Fact>]
let ``conso finds correcct head``() =
    let res = runEval -1 (fun q ->
        conso q <@ [1;2;3] @> <@ [0;1;2;3] @>
    )
    res =? [0]

[<Fact>]
let ``conso finds correct tail``() =
    let res = runEval -1 (fun q ->
        conso <@ 0 @> q <@ [0;1;2;3] @>
    )
    res =? [ [1;2;3] ]

[<Fact>]
let ``conso finds correct tail if it is empty list``() =
    let res : int list list = runEval -1 (fun q ->
        conso <@ 0 @> q <@ [0] @>
    )
    res =? [ [] ]

[<Fact>]
let ``conso finds correct result``() =
    let res = runEval -1 (fun q ->
        conso <@ 0 @> <@ [1;2;3] @> q
    )
    res =? [ [0;1;2;3] ]

[<Fact>]
let ``conso finds correct combination of head and tail``() =
    let res = runEval -1 (fun q ->
        let h,t = fresh(),fresh()
        conso h t <@ [1;2;3] @>
        &&& equiv <@ %h,%t @> q
    )
    res =? [ 1,[2;3] ]

[<Fact>]
let ``appendo finds correct prefix``() =
    let res = runEval -1 (fun q -> appendo q <@ [5; 4] @> <@ [2; 3; 5; 4] @>)
    res =? [ [2; 3] ]

[<Fact>]
let ``appendo finds correct postfix``() =
    let res = runEval -1 (fun q -> appendo <@ [3; 5] @> q <@ [3; 5; 4; 3] @>)
    res =? [ [4; 3] ]

[<Fact>]
let ``appendo finds empty postfix``() =
    let res : int list list = runEval -1 (fun q -> appendo <@ [3; 5] @> q <@ [3; 5] @>)
    res =? [ [] ]

[<Fact>]
let ``appendo finds correct number of prefix and postfix combinations``() =
    let res = runEval -1 (fun q -> 
        let l,s = fresh(),fresh()
        appendo l s <@ [1; 2; 3] @>
        &&& equiv <@ (%l, %s) @> q)
    res =? [  [], [1;2;3]
              [1], [2;3]
              [1;2], [3]
              [1;2;3], []
           ]

[<Fact>]
let projectTest() = 
    let res = run -1 (fun q -> 
        let x = fresh()
        equiv <@ 5 @> x
        &&& (project x (fun xv -> let prod = xv * xv in equiv <@ prod @> q)))
    [ <@ 25 @> :> Expr] =? res

[<Fact>]
let copyTermTest() =
    let g = run -1 (fun q ->
        let (w,x,y,z) = fresh(),fresh(),fresh(),fresh()
        equiv <@ "a", %x, 5, %y, %x @> w
        &&& copyTerm w z
        &&& equiv <@ %w, %z @> q)
    let result = <@ let _0,_1,_2,_3 = obj(),obj(),obj(),obj() in ("a", _0, 5, _1, _0), ("a", _2, 5, _3, _2) @> |> getResult
    sprintf "%A" g =? sprintf "%A" [ result ]

[<Fact>]
let ``conda commits to the first clause if its head succeeds``() =
    let res = runEval -1 (fun q ->
        conda [ [ equiv <@ "olive" @> q] 
                [ equiv <@ "oil" @> q]
        ])
    res =? ["olive"]

[<Fact>]
let ``conda fails if a subsequent clause fails``() =
    let res = runEval -1 (fun q ->
        conda [ [ equiv <@ "virgin" @> q; equiv <@ false @> <@ true @>] 
                [ equiv <@ "olive" @> q] 
                [ equiv <@ "oil" @> q]
        ])
    res =? []

[<Fact>]
let ``conde succeeds each goal at most once``() =
    let res = runEval -1 (fun q ->
        condu [
            [ equiv <@ false @> <@ true @> ]
            [ alwayso ]
        ]
        &&& equiv <@ true @> q)
    res =? [true]

[<Fact>]
let ``onceo succeeds the goal at most once``() =
    let res = run -1 (fun q -> onceo alwayso)
    res.Length =? 1
