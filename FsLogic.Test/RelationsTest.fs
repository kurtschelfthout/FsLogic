
module FsLogic.Test.RelationsTest

open Expecto
open FsLogic
open FsLogic.Substitution
open FsLogic.Goal
open FsLogic.Relations
open Swensen.Unquote

[<Tests>]
let tests =
    testList "Relations" [
        testCase "should unify with int" (fun _ ->
            let res = run -1 (fun q ->  q *=* 1Z)
            res =! [ Det 1 ]
        )

        testCase "should unify with var unified with int" (fun _ ->
            let goal q =
                let x = fresh()
                x *=* 1Z &&& q *=* x
            let res = run -1 goal
            res =! [ Det 1 ]
        )

        testCase "should unify with var unified with int 2" (fun _ ->
            let res =
                run -1 (fun q ->
                    let y = fresh()
                    y *=* q &&& 3Z *=* y)
            res =! [ Det 3 ]
        )

        testCase "should unify list of vars" (fun _ ->
            let res =
                run -1 (fun q ->
                    let (x,y,z) = fresh()
                    q *=* ofList [x; y; z; x]
                    ||| q *=* ofList [z; y; x; z])
            let expected = Half [ Free -3; Free -1; Free -2; Free -3 ]
            res =! [ expected; expected ]
        )

        testCase "should unify list of vars (2)" (fun _ ->
            let res =
                run -1 (fun q ->
                    let x,y = fresh()
                    ofList [x; y] *=* q
                    ||| ofList [y; y] *=* q)
            res.Length =! 2
            let expected0 = Half [Free  0; Free -1]
            let expected1 = Half [Free -1; Free -1]
            res =! [ expected0; expected1 ]
        )

        testCase "disequality constraint" (fun _ ->
            let res = run -1 (fun q ->
                all [ q *=* 5Z
                      q *<>* 5Z ])
            res.Length =! 0
        )

        testCase "disequality constraint 2" (fun _ ->
            let res = run -1 (fun q ->
                let x = fresh()
                all [ q *=* x
                      q *<>* 6Z ])
            res.Length =! 1
        )

        testCase "infinite" (fun _ ->
            let res = run 7 (fun q ->
                        let rec loop() =
                            conde [ [ ~~false *=* q ]
                                    [ q *=* ~~true  ]
                                    [ recurse loop  ]
                                ]
                        loop())
            res =! ([ false; true; false; true; false; true; false] |> List.map (box >> Det))
        )

        testCase "anyoTest" (fun _ ->
            let res = run 5 (fun q -> anyo (~~false *=* q) ||| ~~true *=* q)
            res =! ([true; false; false; false; false] |> List.map (box >> Det))
        )

        testCase "anyoTest2" (fun _ ->
            let res = run 5 (fun q ->
                anyo (1Z *=* q
                    ||| 2Z *=* q
                    ||| 3Z *=* q))
            res =! ([1; 3; 1; 2; 3] |> List.map (box >> Det))
        )

        testCase "alwaysoTest" (fun _ ->
            let res = run 5 (fun x ->
                (~~true *=* x ||| ~~false *=* x)
                &&& alwayso
                &&& ~~false *=* x)
            res =! ([false; false; false; false; false] |> List.map (box >> Det))
        )

        testCase "neveroTest" (fun _ ->
            let res = run 3 (fun q -> //more than 3 will diverge...
                1Z *=* q
                ||| nevero
                ||| 2Z *=* q
                ||| nevero
                ||| 3Z *=* q)
            res =! ([1; 3; 2] |> List.map (box >> Det))
        )

        testCase "conso finds correct head" (fun _ ->
            let res = run -1 (fun q ->
                conso q ~~[1Z; 2Z; 3Z] ~~[0Z; 1Z; 2Z; 3Z]
            )
            res =! [ Det 0 ]
        )

        testCase "conso finds correct tail" (fun _ ->
            let res = run -1 (fun q ->
                conso 0Z q ~~[0Z;1Z;2Z;3Z]
            )
            res =! [ Det [1;2;3] ]
        )

        testCase "conso finds correct tail if it is empty list" (fun _ ->
            let res = run -1 (fun q ->
                conso 0Z q (cons 0Z nil)
            )
            res =! [ Det List.empty<int> ]
        )

        testCase "conso finds correct result" (fun _ ->
            let res = run -1 (fun q ->
                conso 0Z ~~[1Z;2Z;3Z] q
            )
            res =! [ Det [0;1;2;3] ]
        )

        testCase "conso finds correct combination of head and tail" (fun _ ->
            let res = run -1 (fun q ->
                let h,t = fresh()
                conso h t ~~[1Z;2Z;3Z]
                &&& ~~(h,t) *=* q
            )
            res =! [ Det (1,[2;3]) ]
        )

        testCase "appendo finds correct prefix" (fun _ ->
            let res = run -1 (fun q -> appendo q ~~[5Z; 4Z] ~~[2Z; 3Z; 5Z; 4Z])
            res =! [ Det [2; 3] ]
        )

        testCase "appendo finds correct postfix" (fun _ ->
            let res = run -1 (fun q -> appendo ~~[3Z; 5Z] q ~~[3Z; 5Z; 4Z; 3Z])
            res =! [ Det [4; 3] ]
        )

        testCase "appendo finds empty postfix" (fun _ ->
            let res = run -1 (fun q -> appendo ~~[3Z; 5Z] q ~~[3Z; 5Z])
            res =! [ Det List.empty<int> ] //can't use [] because then won't compare equals, type will be 'a list not int list.
        )

        testCase "appendo finds correct number of prefix and postfix combinations" (fun _ ->
            let res = run -1 (fun q ->
                let l,s = fresh()
                appendo l s ~~[1Z; 2Z; 3Z]
                &&& ~~(l, s) *=* q)
            res =! ([ [], [1;2;3]
                      [1], [2;3]
                      [1;2], [3]
                      [1;2;3], []
                    ] |> List.map (box >> Det))
        )

        testCase "removeo removes first occurence of elements from list" (fun _ ->
            let res = run -1 (fun q -> removeo 2Z ~~[1;2;3;4] q)
            res =! [ Det [1;3;4] ]
        )

        testCase "removeo removes element from singleton list" (fun _ ->
            let res = run -1 (fun q -> removeo 2Z ~~[2] q)
            res =! [ Det List.empty<int> ]
        )

        testCase "projectTest" (fun _ ->
            let res = run -1 (fun q ->
                let x = fresh()
                5Z *=* x
                &&& (project x (fun xv -> let prod = xv * xv in ~~prod *=* q)))
            [ Det 25 ] =! res
        )

        testCase "copyTermTest" (fun _ ->
            let g = run -1 (fun q ->
                let w,x,y,z = fresh()
                ~~(~~"a", x, 5Z, y, x) *=* w
                &&& copyTerm w z
                &&&  ~~(w, z) *=* q)
            g =! [Half
                    [Half [Det "a"; Free -2; Det 5; Free -1; Free -2];
                    Half [Det "a"; Free -5; Det 5; Free -4; Free -5]]]
        )

        testCase "conda commits to the first clause if its head succeeds" (fun _ ->
            let res = run -1 (fun q ->
                conda [ [ ~~"olive" *=* q ]
                        [ ~~"oil" *=* q ]
                ])
            res =! [Det "olive"]
        )

        testCase "conda fails if a subsequent clause fails" (fun _ ->
            let res = run -1 (fun q ->
                conda [ [ ~~"virgin" *=* q; fail ]
                        [ ~~"olive" *=* q ]
                        [ ~~"oil" *=* q ]
                ])
            res =! []
        )

        testCase "conde succeeds each goal at most once" (fun _ ->
            let res = run -1 (fun q ->
                condu [ [ fail ]
                        [ alwayso ]
                    ]
                &&& ~~true *=* q)
            res =! [Det true]
        )

        testCase "onceo succeeds the goal at most once" (fun _ ->
            let res = run -1 (fun _ -> onceo alwayso)
            res.Length =! 1
        )
]