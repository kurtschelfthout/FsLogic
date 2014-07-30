module MiniKanren.Main

open Examples

[<EntryPoint>]
let main args =
    printfn "%O" bla
    printfn "%O" g
    printfn "%O" g2
    printfn "%O" g3
    printfn "%O" g4
    printfn "%O" infinite
    printfn "%O" anyTest
    printfn "%O" anyTest2
    printfn "%O" alwaysoTest
    printfn "%O" alwaysoTest2
    printfn "%A" appendoTest
    printfn "%A" appendoTest2
    System.Console.ReadKey() |> ignore
    0

