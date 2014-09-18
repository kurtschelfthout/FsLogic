
module Tests

open MiniKanren.Goal
open MiniKanren.Substitution
open MiniKanren.Relations
open Xunit
open Swensen.Unquote

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
    //printf "%s"  (res |> List.map Operators.decompile |> String.concat ";")
    Assert.Equal(2, res.Length)

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
    Assert.Equal(2, res.Length)

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
let appendoTest() =
    let res = run 1 (fun q -> appendo q <@ [5; 4] @> <@ [3; 5; 4] @>)
    (res |> List.map Operators.evalRaw) =? [ [3] ]

[<Fact>]
let appendoTest2() =
    let res = run 3 (fun q -> 
        let l,s = fresh(),fresh()
        appendo l s <@ [1; 2] @>
        &&& equiv <@ ([%l; %s]) @> q)
    Assert.Equal(3, res.Length)
//
//[<Fact>]
//let projectTest() = 
//    let res = run 5 (fun q -> 
//        let x = fresh()
//        equiv (Atom 5) x
//        &&& (project x (fun (Atom xv) -> equiv (Atom (xv*xv)) q)))
//    Assert.Equal<_ list>([Atom 25], res)
//
