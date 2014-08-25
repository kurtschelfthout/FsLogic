
module Tests

open MiniKanren.Goal
open MiniKanren.Substitution
open MiniKanren.Relations
open Xunit
open Swensen.Unquote

let upcastL l = l |> List.map (fun e -> e :> IUnify)

[<Fact>]
let g0() = 
    let goal q = 
        let x = fresh() 
        equiv x (Atom 3)
        &&& equiv q x
    let res = run 5 goal
    res =? [Atom 3]

[<Fact>]
let g1() = 
    let res = run 5 (fun x -> equiv x (Atom 1))
    res =? [Atom 1]

[<Fact>]
let g2() = 
    let res = 
        run 5 (fun q -> 
            let (x,y,z) = fresh<Atom<int>>(),fresh<Atom<int>>(),fresh<Atom<int>>()
            equiv (LList<Atom<int>>.FromSeq [x; y; z; x]) q
            ||| equiv (LList<Atom<int>>.FromSeq [z; y; x; z]) q)
    Assert.Equal(2, res.Length)

[<Fact>]
let g3() = 
    let res = 
        run 1 (fun q -> 
            let y = fresh()
            equiv y q &&& equiv (Atom 3) y)
    res =? [Atom 3]

[<Fact>]
let g4() = 
    let res = 
        run 5 (fun q -> 
            let x,y,z = fresh<Atom<int>>(),fresh<Atom<int>>(),fresh<Atom<int>>()
            equiv (LList.FromSeq [x; y]) q
            ||| equiv (LList.FromSeq [y; y]) q)
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
    res =? [Atom false;Atom true;Atom false;Atom true;Atom false;Atom true;Atom false]


[<Fact>]
let anyoTest() = 
    let res = run 5 (fun q -> anyo (equiv (Atom false) q) ||| 
                                    equiv (Atom true) q)
    res =? [Atom true;Atom false;Atom false;Atom false;Atom false]

[<Fact>]
let anyoTest2() =  
    let res = run 5 (fun q -> 
        anyo (equiv (Atom 1) q
              ||| equiv (Atom 2) q
              ||| equiv (Atom 3) q))
    res =? [Atom 1;Atom 3;Atom 1;Atom 2;Atom 3]

[<Fact>]
let alwaysoTest() =
    let res = run 5 (fun x ->
        (equiv (Atom true) x ||| equiv (Atom false) x)
        &&& alwayso
        &&& equiv (Atom false) x)
    res =? [Atom false;Atom false;Atom false;Atom false;Atom false]

[<Fact>]
let neveroTest() =
    let res = run 3 (fun q -> //more than 3 will diverge...
        equiv (Atom 1) q
        ||| nevero
        ||| (equiv (Atom 2) q
        ||| nevero
        ||| equiv (Atom 3) q)) 
    res =? [Atom 1; Atom 2; Atom 3]

[<Fact>]
let appendoTest() =
    let res = run 1 (fun q -> appendo q (LList.FromSeq [Atom 5; Atom 4]) (LList.FromSeq [Atom 3; Atom 5; Atom 4]))
    res =? [Cons(Atom 3, Nil)]

[<Fact>]
let appendoTest2() =
    let res = run 3 (fun q -> 
        let l,s = fresh(),fresh()
        appendo l s (Cons (Atom 1, Cons(Atom 2, Nil)))
        &&& equiv (Cons (l,Cons(s,Nil))) q)
    Assert.Equal(3, res.Length)

//[<Fact>]
//let projectTest() = 
//    let (|Int|) (x:obj) = x :?> int32
//    let res = run 5 (fun q -> 
//        let x = fresh()
//        equiv (Atom 5) x
//        &&& (project x (fun (Int xv) -> equiv (Atom (xv*xv)) q)))
//    Assert.Equal<_ list>([Atom 25], res)

