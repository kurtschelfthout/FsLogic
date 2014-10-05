
module Tests

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
    let goal q = 
        let x = fresh() 
        x -=- 3 
        &&& equiv q x
    let res = runEval 5 goal
    res =? [ 3 ]

[<Fact>]
let g1() = 
    let res = runEval 5 (fun x ->  x -=- 1)
    res =? [ 1 ]

[<Fact>]
let g2() = 
    let res = 
        run 5 (fun q -> 
            let (x,y,z) = fresh(),fresh(),fresh()
            equiv <@ [%x; %y; %z; %x] @> q
            ||| equiv <@ [%z; %y; %x; %z] @> q)
    2 =? res.Length

[<Fact>]
let g3() = 
    let res = 
        runEval 1 (fun q -> 
            let y = fresh()
            equiv y q &&& 3 -=- y)
    res =? [3]

[<Fact>]
let g4() = 
    let res = 
        run 5 (fun q -> 
            let x,y,z = fresh(),fresh(),fresh()
            equiv <@ [x; y] @> q
            ||| equiv <@ [y; y] @> q)
    2 =? res.Length

[<Fact>]
let infinite() = 
    let res = runEval 7 (fun q ->  
                let rec loop() =
                    conde [ [ false -=- q ]
                            [ q -=- true  ]
                            [ recurse loop] ]
                loop())
    res =? [ false; true; false; true; false; true; false]


[<Fact>]
let anyoTest() = 
    let res = runEval 5 (fun q -> anyo (false -=- q) ||| true -=- q)
    res =? [true; false; false; false; false]

[<Fact>]
let anyoTest2() =  
    let res = runEval 5 (fun q -> 
        anyo (1 -=- q
              ||| 2 -=- q
              ||| 3 -=- q))
    res =? [1; 3; 1; 2; 3]

[<Fact>]
let alwaysoTest() =
    let res = runEval 5 (fun x ->
        (true -=- x ||| false -=- x)
        &&& alwayso
        &&& false -=- x)
    res =? [false; false; false; false; false]

[<Fact>]
let neveroTest() =
    let res = runEval 3 (fun q -> //more than 3 will diverge...
        1 -=- q
        ||| nevero
        ||| 2 -=- q
        ||| nevero
        ||| 3 -=- q) 
    res =? [1; 3; 2]

[<Fact>]
let ``conso finds correcct head``() =
    let res = runEval 1 (fun q ->
        conso q <@ [1;2;3] @> <@ [0;1;2;3] @>
    )
    res =? [0]

[<Fact>]
let ``conso finds correct tail``() =
    let res = runEval 1 (fun q ->
        conso <@ 0 @> q <@ [0;1;2;3] @>
    )
    res =? [ [1;2;3] ]

[<Fact>]
let ``conso finds correct tail if it is empty list``() =
    let res : int list list = runEval 1 (fun q ->
        conso <@ 0 @> q <@ [0] @>
    )
    res =? [ [] ]

[<Fact>]
let ``conso finds correct result``() =
    let res = runEval 1 (fun q ->
        conso <@ 0 @> <@ [1;2;3] @> q
    )
    res =? [ [0;1;2;3] ]

[<Fact>]
let ``conso finds correct combination of head and tail``() =
    let res = runEval 100 (fun q ->
        let h,t = fresh(),fresh()
        conso h t <@ [1;2;3] @>
        &&& equiv <@ %h,%t @> q
    )
    //res.Length =? 1
    res =? [ 1,[2;3] ]

[<Fact>]
let ``appendo finds correct prefix``() =
    let res = runEval 1 (fun q -> appendo q <@ [5; 4] @> <@ [2; 3; 5; 4] @>)
    res =? [ [2; 3] ]

[<Fact>]
let ``appendo finds correct postfix``() =
    let res = runEval 1 (fun q -> appendo <@ [3; 5] @> q <@ [3; 5; 4; 3] @>)
    res =? [ [4; 3] ]

[<Fact>]
let ``appendo finds empty postfix``() =
    let res : int list list = runEval 1 (fun q -> appendo <@ [3; 5] @> q <@ [3; 5] @>)
    res =? [ [] ]

[<Fact>]
let ``appendo finds correct number of prefix and postfix combinations``() =
    let res = runEval 5 (fun q -> 
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
    let res = runEval 5 (fun q -> 
        let x = fresh()
        5 -=- x
        &&& (project x (fun xv -> xv*xv -=- q)))
    [25] =? res

[<Fact>]
let copyTermTest() =
    let g = run 2 (fun q ->
        let (w,x,y,z) = fresh(),fresh(),fresh(),fresh()
        equiv <@ "a", %x, 5, %y, %x @> w
        &&& copyTerm w z
        &&& equiv <@ %w, %z @> q)
    let result = <@ let _0,_1,_2,_3 = obj(),obj(),obj(),obj() in ("a", _0, 5, _1, _0), ("a", _2, 5, _3, _2) @> |> getResult
    sprintf "%A" g =? sprintf "%A" [ result ]