namespace MiniKanren

module internal Option =
    let defaultTo a opt =
        match opt with
        | None -> a
        | Some a -> a

[<AutoOpen>]
module internal Util =     
    let curry f = fun a b -> f (a,b)
    let uncurry f = fun (a,b) -> f a b