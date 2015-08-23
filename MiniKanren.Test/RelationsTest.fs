
module RelationsTest

open MiniKanren
open MiniKanren.Goal
open MiniKanren.Substitution
open MiniKanren.Relations
open Xunit
open Swensen.Unquote

//let toUni (l:Term<'a> list) = l |> List.map (fun x -> x.Uni)

[<Fact>]
let g0() = 
    let goal q = 
        let x = fresh() 
        x *=* 3Z &&& q *=* x
    let res = run -1 goal
    res =! [ Some 3 ]

[<Fact>]
let g1() = 
    let res = run -1 (fun q ->  q *=* 1Z)
    res =! [ Some 1 ]

[<Fact>]
let g2() = 
    let res = 
        run -1 (fun q -> 
            let (x,y,z) = fresh()
            equiv q (ofList [x; y; z; x])
            ||| equiv q (ofList [z; y; x; z]))
    2 =! res.Length
    res =! [ None; None]
    //numbering restarts with each value
    //let expected = [ _0;_1;_2;_0 ]  
    //sprintf "%A" [ expected; expected ] =! sprintf "%A" res

[<Fact>]
let g3() = 
    let res = 
        run -1 (fun q -> 
            let y = fresh()
            equiv y q &&& equiv 3Z y)
    res =! [ Some 3 ]

[<Fact>]
let g4() = 
    let res = 
        run -1 (fun q -> 
            let x,y,z = fresh()
            ofList [x; y] *=* q
            ||| ofList [y; y] *=* q)
    2 =! res.Length
//    let expected0 = <@ let _0,_1 =fresh(),fresh() in [ _0;_1 ] @> |> getResult
//    let expected1 = <@ let _0 =fresh() in [ _0;_0 ] @> |> getResult
//    sprintf "%A" [ expected0; expected1 ] =! sprintf "%A" res

[<Fact>]
let infinite() = 
    let res = run 7 (fun q ->  
                let rec loop() =
                    conde [ [ ~~false *=* q ]
                            [ q *=* ~~true  ]
                            [ recurse loop  ] 
                        ]
                loop())
    res =! ([ false; true; false; true; false; true; false] |> List.map Some)


[<Fact>]
let anyoTest() = 
    let res = run 5 (fun q -> anyo (~~false *=* q) ||| ~~true *=* q)
    res =! ([true; false; false; false; false] |> List.map Some)

[<Fact>]
let anyoTest2() =  
    let res = run 5 (fun q -> 
        anyo (1Z *=* q
              ||| 2Z *=* q
              ||| 3Z *=* q))
    res =! ([1; 3; 1; 2; 3] |> List.map Some)

[<Fact>]
let alwaysoTest() =
    let res = run 5 (fun x ->
        (~~true *=* x ||| ~~false *=* x)
        &&& alwayso
        &&& ~~false *=* x)
    res =! ([false; false; false; false; false] |> List.map Some)

[<Fact>]
let neveroTest() =
    let res = run 3 (fun q -> //more than 3 will diverge...
        1Z *=* q
        ||| nevero
        ||| 2Z *=* q
        ||| nevero
        ||| 3Z *=* q) 
    res =! ([1; 3; 2] |> List.map Some)

[<Fact>]
let ``conso finds correct head``() =
    let res = run -1 (fun q ->
        conso q ~~[1Z; 2Z; 3Z] ~~[0Z; 1Z; 2Z; 3Z]
    )
    res =! [ Some 0 ]

[<Fact>]
let ``conso finds correct tail``() =
    let res = run -1 (fun q ->
        conso 0Z q ~~[0Z;1Z;2Z;3Z]
    )
    res =! [ Some [1;2;3] ]

[<Fact>]
let ``conso finds correct tail if it is empty list``() =
    let res = run -1 (fun q ->
        conso 0Z q (cons 0Z nil)
    )
    res =! [ Some [] ]

[<Fact>]
let ``conso finds correct result``() =
    let res = run -1 (fun q ->
        conso 0Z ~~[1Z;2Z;3Z] q
    )
    res =! [ Some [0;1;2;3] ]

[<Fact>]
let ``conso finds correct combination of head and tail``() =
    let res = run -1 (fun q ->
        let h,t = fresh()
        conso h t ~~[1Z;2Z;3Z]
        &&& ~~(h,t) *=* q
    )
    res =! [ Some (1,[2;3]) ]

[<Fact>]
let ``appendo finds correct prefix``() =
    let res = run -1 (fun q -> appendo q ~~[5Z; 4Z] ~~[2Z; 3Z; 5Z; 4Z])
    res =! [ Some [2; 3] ]


[<Fact>]
let ``appendo finds correct postfix``() =
    let res = run -1 (fun q -> appendo ~~[3Z; 5Z] q ~~[3Z; 5Z; 4Z; 3Z])
    res =! [ Some [4; 3] ]

[<Fact>]
let ``appendo finds empty postfix``() =
    let res = run -1 (fun q -> appendo ~~[3Z; 5Z] q ~~[3Z; 5Z])
    res =! [ Some [] ]

[<Fact>]
let ``appendo finds correct number of prefix and postfix combinations``() =
    let res = run -1 (fun q -> 
        let l,s = fresh()
        appendo l s ~~[1Z; 2Z; 3Z]
        &&& ~~(l, s) *=* q)
    res =! ([ [], [1;2;3]
              [1], [2;3]
              [1;2], [3]
              [1;2;3], []
            ] |> List.map Some)

[<Fact>]
let projectTest() = 
    let res = run -1 (fun q -> 
        let x = fresh()
        5Z *=* x
        &&& (project x (fun xv -> let prod = xv * xv in ~~prod *=* q)))
    [ Some 25 ] =! res

//TODO
//[<Fact>]
//let copyTermTest() =
//    let g = run -1 (fun q ->
//        let (w,x,y,z) = fresh(),fresh(),fresh(),fresh()
//        equiv <@ "a", %x, 5, %y, %x @> w
//        &&& copyTerm w z
//        &&& equiv <@ %w, %z @> q)
//    let result = <@ let _0,_1,_2,_3 = obj(),obj(),obj(),obj() in ("a", _0, 5, _1, _0), ("a", _2, 5, _3, _2) @> |> getResult
//    sprintf "%A" g =! sprintf "%A" [ result ]

[<Fact>]
let ``conda commits to the first clause if its head succeeds``() =
    let res = run -1 (fun q ->
        conda [ [ ~~"olive" *=* q] 
                [ ~~"oil" *=* q]
        ])
    res =! [Some "olive"]

[<Fact>]
let ``conda fails if a subsequent clause fails``() =
    let res = run -1 (fun q ->
        conda [ [ ~~"virgin" *=* q; ~~false *=* ~~true] 
                [ ~~"olive" *=* q] 
                [ ~~"oil" *=* q]
        ])
    res =! []

[<Fact>]
let ``conde succeeds each goal at most once``() =
    let res = run -1 (fun q ->
        condu [ [ ~~false *=* ~~true ]
                [ alwayso ]
              ]
        &&& ~~true *=* q)
    res =! [Some true]

[<Fact>]
let ``onceo succeeds the goal at most once``() =
    let res = run -1 (fun q -> onceo alwayso)
    res.Length =! 1
