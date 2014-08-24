
module Tests

open MiniKanren.Goal
open MiniKanren.Substitution
open MiniKanren.Relations
open Xunit

[<Fact>]
let g0() = 
    let goal q = 
        let x = fresh() 
        equiv x (Atom 3)
        &&& equiv q x
    let res = run 5 goal
    Assert.Equal<_ list>([Atom 3], res)

[<Fact>]
let g1() = 
    let res = run 5 (fun x -> equiv x (Atom 1))
    Assert.Equal<_ list>([Atom 1], res)

[<Fact>]
let g2() = 
    let res = 
        run 5 (fun q -> 
            let (x,y,z) = fresh(),fresh(),fresh()
            equiv (Term.FromSeq [x; y; z; x]) q
            ||| equiv (Term.FromSeq [z; y; x; z]) q)
    Assert.Equal(2, res.Length)

[<Fact>]
let g3() = 
    let res = 
        run 1 (fun q -> 
            let x,y = fresh(),fresh()
            equiv y q &&& equiv (Atom 3) y)
    Assert.Equal<_ list>([Atom 3], res)

[<Fact>]
let g4() = 
    let res = 
        run 5 (fun q -> 
            let x,y,z = fresh(),fresh(),fresh()
            equiv (List (x, y)) q
            ||| equiv (List (y, y)) q)
    Assert.Equal(2, res.Length)

[<Fact>]
let infinite() = 
    let res = run 7 (fun q ->  
                let rec loop() =
                    conde <|
                        seq { yield equiv (Atom false) q, []
                              yield equiv (Atom true)  q, []
                              yield loop(),[] }
                loop())
    Assert.Equal<_ list>([Atom false;Atom true;Atom false;Atom true;Atom false;Atom true;Atom false], res)


[<Fact>]
let anyoTest() = 
    let res = run 5 (fun q -> anyo (equiv (Atom false) q) ||| 
                                    equiv (Atom true) q)
    Assert.Equal<_ list>([Atom true;Atom false;Atom false;Atom false;Atom false], res)

[<Fact>]
let anyoTest2() =  
    let res = run 5 (fun q -> 
        anyo (equiv (Atom 1) q
              ||| equiv (Atom 2) q
              ||| equiv (Atom 3) q))
    Assert.Equal<_ list>([Atom 1;Atom 3;Atom 1;Atom 2;Atom 3], res)

[<Fact>]
let alwaysoTest() =
    let res = run 5 (fun x ->
        (equiv (Atom true) x ||| equiv (Atom false) x)
        &&& alwayso
        &&& equiv (Atom false) x)
    Assert.Equal<_ list>([Atom false;Atom false;Atom false;Atom false;Atom false], res)

[<Fact>]
let neveroTest() =
    let res = run 3 (fun q -> //more than 3 will diverge...
        equiv (Atom 1) q
        ||| nevero
        ||| (equiv (Atom 2) q
        ||| nevero
        ||| equiv (Atom 3) q)) 
    Assert.Equal<_ list>([Atom 1; Atom 2; Atom 3], res)

[<Fact>]
let appendoTest() =
    let res = run 1 (fun q -> appendo q (List (Atom 5, List(Atom 4, Nil))) (List (Atom 3, List (Atom 5, List(Atom 4, Nil)))))
    Assert.Equal<_ list>([List(Atom 3, Nil)],res)

[<Fact>]
let appendoTest2() =
    let res = run 3 (fun q -> 
        let l,s = fresh(),fresh()
        appendo l s (List (Atom 1, List(Atom 2,Nil)))
        &&& equiv (List (l,s)) q)
    Assert.Equal(3, res.Length)

[<Fact>]
let projectTest() = 
    let (|Int|) (x:obj) = x :?> int32
    let res = run 5 (fun q -> 
        let x = fresh()
        equiv (Atom 5) x
        &&& (project x (fun (Int xv) -> equiv (Atom (xv*xv)) q)))
    Assert.Equal<_ list>([Atom 25], res)

